import ImbalancedChen.SingletonPrimeProductTransportP5
import Mathlib.NumberTheory.Divisors

/-!
# Finite endpoint payment for the original singleton prime

The same signed physical rho is kept throughout. An endpoint perturbation
supported at nonzero distance at most D from N costs at most twice the
literal divisor summatory function, plus its exact coprime-mean payment.
No smooth PP theorem, divisor asymptotic or adopted density is assumed.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5OriginalPrimeEndpoint

noncomputable section
open scoped BigOperators
open Classical

/-- This natural distance keeps both sides of the smoothed prime endpoint. -/
def distance (N p : ℕ) : ℕ := if p ≤ N then N - p else p - N

theorem distance_pos {N p : ℕ} (hp : p ≠ N) : 0 < distance N p := by
  unfold distance
  split_ifs <;> omega

theorem modEq_iff_dvd_distance (N p q : ℕ) :
    Nat.ModEq q p N ↔ q ∣ distance N p := by
  unfold distance
  split_ifs with hp
  · exact (dvd_sub_iff_modEq_of_le hp).symm
  · constructor
    · intro h
      exact (dvd_sub_iff_modEq_of_le (by omega : N ≤ p)).mpr h.symm
    · intro h
      exact ((dvd_sub_iff_modEq_of_le (by omega : N ≤ p)).mp h).symm

/-- A positive distance has at most two preimages, even if D exceeds N. -/
theorem distance_fiber_card_le_two (S : Finset ℕ) (N n : ℕ) :
    ((S.filter (fun p => distance N p = n)).card : ℝ) ≤ 2 := by
  have hsub : S.filter (fun p => distance N p = n) ⊆ {N-n,N+n} := by
    intro p hp
    have heq := (Finset.mem_filter.mp hp).2
    unfold distance at heq
    by_cases hle : p ≤ N
    · rw [if_pos hle] at heq
      have h : p = N-n := by omega
      simp [h]
    · rw [if_neg hle] at heq
      have h : p = N+n := by omega
      simp [h]
  have hcard : (S.filter (fun p => distance N p = n)).card ≤ 2 := by
    calc
      _ ≤ ({N-n,N+n} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by by_cases h : N-n = N+n <;> simp [h]
  exact_mod_cast hcard

/-- Positive radial summation loses only the two sides of the endpoint. -/
theorem sum_distance_le_two_sum (S : Finset ℕ) (N D : ℕ) (f : ℕ → ℝ)
    (hS : ∀ p ∈ S, p ≠ N ∧ distance N p ≤ D)
    (hf : ∀ n ∈ Finset.Icc 1 D, 0 ≤ f n) :
    (∑ p ∈ S, f (distance N p)) ≤ 2 * ∑ n ∈ Finset.Icc 1 D, f n := by
  have hmap : ∀ p ∈ S, distance N p ∈ Finset.Icc 1 D := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨distance_pos (hS p hp).1,(hS p hp).2⟩
  have hF := Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.Icc 1 D)
    (g := distance N) hmap (fun p => f (distance N p))
  rw [← hF,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have heq : (∑ p ∈ S with distance N p = n, f (distance N p)) =
      ((S.filter (fun p => distance N p = n)).card : ℝ) * f n := by
    calc
      _ = ∑ p ∈ S with distance N p = n, f n := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = _ := by simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right (distance_fiber_card_le_two S N n) (hf n hn)

theorem endpoint_card_le (S : Finset ℕ) (N D : ℕ)
    (hS : ∀ p ∈ S, p ≠ N ∧ distance N p ≤ D) :
    (S.card : ℝ) ≤ 2 * (D : ℝ) := by
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc,
    Nat.add_sub_cancel] using
    sum_distance_le_two_sum S N D (fun _ => 1) hS (fun _ _ => zero_le_one)

/-- One endpoint integer pays only divisors of its nonzero distance. -/
theorem sum_abs_rho_congruence_le_divisors (Q : Finset ℕ) (rho : ℕ → ℝ)
    (N p : ℕ) (hp : p ≠ N) (hrho : ∀ q ∈ Q, |rho q| ≤ 1) :
    (∑ q ∈ Q with Nat.ModEq q p N, |rho q|) ≤
      ((distance N p).divisors.card : ℝ) := by
  have hsub : Q.filter (fun q => Nat.ModEq q p N) ⊆ (distance N p).divisors := by
    intro q hq
    exact Nat.mem_divisors.mpr ⟨(modEq_iff_dvd_distance N p q).mp
      (Finset.mem_filter.mp hq).2,ne_of_gt (distance_pos hp)⟩
  calc
    _ ≤ ∑ q ∈ Q with Nat.ModEq q p N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hrho q (Finset.mem_filter.mp hq).1
    _ = ((Q.filter (fun q => Nat.ModEq q p N)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- No prime counting or positivity of rho is used in this endpoint bound. -/
theorem abs_signed_congruence_endpoint_le (S Q : Finset ℕ) (rho delta : ℕ → ℝ)
    (N D : ℕ) (hS : ∀ p ∈ S, p ≠ N ∧ distance N p ≤ D)
    (hrho : ∀ q ∈ Q, |rho q| ≤ 1) (hdelta : ∀ p ∈ S, |delta p| ≤ 1) :
    |∑ q ∈ Q, rho q * finiteCongruenceMass S delta N q| ≤
      2 * ∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ) := by
  have heq : (∑ q ∈ Q, rho q * finiteCongruenceMass S delta N q) =
      ∑ p ∈ S, delta p * ∑ q ∈ Q with Nat.ModEq q p N, rho q := by
    simp only [finiteCongruenceMass,Finset.sum_filter,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    by_cases h : Nat.ModEq q p N <;> simp [h,mul_comm]
  rw [heq]
  calc
    _ ≤ ∑ p ∈ S, |delta p * ∑ q ∈ Q with Nat.ModEq q p N, rho q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, ((distance N p).divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul]
      calc
        _ ≤ 1 * ∑ q ∈ Q with Nat.ModEq q p N, |rho q| :=
          mul_le_mul (hdelta p hp) (Finset.abs_sum_le_sum_abs _ _)
            (abs_nonneg _) (by norm_num)
        _ ≤ _ := by
          rw [one_mul]
          exact sum_abs_rho_congruence_le_divisors Q rho N p (hS p hp).1 hrho
    _ ≤ _ := sum_distance_le_two_sum S N D _ hS (fun _ _ => Nat.cast_nonneg _)

/-- The exact coprime mean is paid without replacing it by the total count. -/
theorem abs_signed_coprime_mean_le (S Q : Finset ℕ) (rho delta : ℕ → ℝ)
    (hdelta : ∀ p ∈ S, |delta p| ≤ 1) :
    |∑ q ∈ Q, rho q * (finiteCoprimeMass S delta q / (Nat.totient q : ℝ))| ≤
      (S.card : ℝ) * ∑ q ∈ Q, |rho q| / (Nat.totient q : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hmass : |finiteCoprimeMass S delta q| ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ S with Nat.Coprime p q, |delta p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S with Nat.Coprime p q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hdelta p (Finset.mem_filter.mp hp).1
      _ ≤ (S.card : ℝ) := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          (show ((S.filter (fun p => Nat.Coprime p q)).card : ℝ) ≤ (S.card : ℝ) from
            by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _))
  rw [abs_mul,abs_div,abs_of_nonneg (Nat.cast_nonneg (Nat.totient q))]
  calc
    _ ≤ |rho q| * ((S.card : ℝ) / (Nat.totient q : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmass (Nat.cast_nonneg _))
        (abs_nonneg _)
    _ = _ := by ring

/-- The finite sharp/smooth correction at the literal primitive PP centre.
This applies to an endpoint-supported difference of tests, with the SAME rho. -/
theorem abs_signed_primitive_endpoint_le (S Q : Finset ℕ) (rho delta : ℕ → ℝ)
    (N D : ℕ) (hS : ∀ p ∈ S, p ≠ N ∧ distance N p ≤ D)
    (hrho : ∀ q ∈ Q, |rho q| ≤ 1) (hdelta : ∀ p ∈ S, |delta p| ≤ 1) :
    |∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy S delta N q| ≤
      2 * ∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ) +
        (S.card : ℝ) * ∑ q ∈ Q, |rho q| / (Nat.totient q : ℝ) := by
  have heq : (∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy S delta N q) =
      (∑ q ∈ Q, rho q * finiteCongruenceMass S delta N q) -
        ∑ q ∈ Q, rho q * (finiteCoprimeMass S delta q / (Nat.totient q : ℝ)) := by
    simp only [finitePrimitiveDiscrepancy,mul_sub,Finset.sum_sub_distrib]
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add
    (abs_signed_congruence_endpoint_le S Q rho delta N D hS hrho hdelta)
    (abs_signed_coprime_mean_le S Q rho delta hdelta))

/-- Uniform in the actual lower policy, cap and cutoffs. At an even centre
greater than two the zero-distance prime is impossible. Both endpoint
sides and the exact coprime mean are retained, before any PNT estimate. -/
theorem actual_causal_prime_endpoint_le
    (retainEven : List ℕ → Bool) (N cap D : ℕ) (w z L : ℝ)
    (S Q : Finset ℕ) (delta : ℕ → ℝ)
    (hEven : Even N) (hN : 2 < N)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hwindow : ∀ p ∈ S, distance N p ≤ D)
    (hdelta : ∀ p ∈ S, |delta p| ≤ 1) :
    |∑ q ∈ Q, actualLowerSmallRoughRho retainEven N cap w z L q *
        finitePrimitiveDiscrepancy S delta N q| ≤
      2 * ∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ) +
        2 * (D : ℝ) * ∑ q ∈ Q,
          |actualLowerSmallRoughRho retainEven N cap w z L q| / (Nat.totient q : ℝ) := by
  have hS : ∀ p ∈ S, p ≠ N ∧ distance N p ≤ D := by
    intro p hp
    refine ⟨?_,hwindow p hp⟩
    intro heq
    have hNp : Nat.Prime N := heq ▸ hprime p hp
    have htwo := hNp.even_iff.mp hEven
    omega
  refine (abs_signed_primitive_endpoint_le S Q _ delta N D hS
    (fun q _ => actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q) hdelta).trans ?_
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_right (endpoint_card_le S N D hS)
    (Finset.sum_nonneg (fun q _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))

/-- Sharp and smooth tests may live on a much larger prime prefix. Only
their actual difference is restricted to the endpoint carrier. The two
rank-one PP targets have exactly the same physical coefficient rho. -/
theorem singleton_test_difference_eq_endpoint
    (P N : ℕ) (S Q : Finset ℕ) (rho sharp smooth : ℕ → ℝ)
    (hS : S ⊆ chenPrimePrefix P)
    (hagree : ∀ p ∈ chenPrimePrefix P, p ∉ S → sharp p = smooth p) :
    Part3.primeProductSignedError 1 P N Q rho (P5S1SingletonPP.singletonWeight P sharp) -
      Part3.primeProductSignedError 1 P N Q rho (P5S1SingletonPP.singletonWeight P smooth) =
        ∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy S (fun p => sharp p-smooth p) N q := by
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq,
    P5S1SingletonPP.primeProductSignedError_singleton_eq,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_sub,← finitePrimitiveDiscrepancy_sub,
    finitePrimitiveDiscrepancy_eq_of_subset S (chenPrimePrefix P) _ N q hS
      (fun p hp hn => sub_eq_zero.mpr (hagree p hp hn))]

/-- Literal original-prime sharp/smooth PP payment for the actual causal
lower coefficient. The analytic smooth-PP and lower-trim bounds remain
separate missing inputs; this theorem supplies their endpoint transfer. -/
theorem actual_causal_singleton_sharp_smooth_le
    (retainEven : List ℕ → Bool) (N cap P D : ℕ) (w z L : ℝ)
    (S Q : Finset ℕ) (sharp smooth : ℕ → ℝ)
    (hEven : Even N) (hN : 2 < N) (hS : S ⊆ chenPrimePrefix P)
    (hwindow : ∀ p ∈ S, distance N p ≤ D)
    (hagree : ∀ p ∈ chenPrimePrefix P, p ∉ S → sharp p = smooth p)
    (hdelta : ∀ p ∈ S, |sharp p-smooth p| ≤ 1) :
    |Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight P sharp) -
      Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight P smooth)| ≤
      2 * ∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ) +
        2 * (D : ℝ) * ∑ q ∈ Q,
          |actualLowerSmallRoughRho retainEven N cap w z L q| / (Nat.totient q : ℝ) := by
  rw [singleton_test_difference_eq_endpoint P N S Q _ sharp smooth hS hagree]
  exact actual_causal_prime_endpoint_le retainEven N cap D w z L S Q _ hEven hN
    (fun p hp => (mem_chenPrimePrefix.mp (hS hp)).2) hwindow hdelta

end
end ImbalancedChen.P5OriginalPrimeEndpoint
