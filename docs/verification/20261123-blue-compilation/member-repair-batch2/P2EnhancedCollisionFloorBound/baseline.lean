import ImbalancedChen.P2EnhancedPrefixMaskDefect
import MathlibNt.Wu2008DoubleSieve.Omega3FiniteError

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The selected-prime collision event is embedded in the existing actual
repeated-divisibility complement carrier at the COMPLETE labelled divisor
d*l.prod. We reuse its exact floor-sum and rough-prime power estimates.
No new unweighted surrogate is substituted for the source event, and no
factor 1/d or marked-tuple multiplicity is dropped.

The new result is per labelled tuple. Summing these estimates over all
original words and sigma-weights, and paying that sum relative to Theta_Q,
are subsequent obligations. No enhanced analytic count licence is assumed.
-/

namespace ImbalancedChen.P2EnhancedCollisionFloorBound

noncomputable section

open Finset Wu2008DoubleSieve
open P2EnhancedPrefixMaskDefect
open scoped Classical

theorem collision_output_lt {N d ell : ℕ} {l : List ℕ}
    (hN : 4 ≤ N) (he : Even N) (hell : ell ∈ collisionCarrier N d l) : ell < N := by
  have hsource := (mem_filter.mp hell).1
  change ell ∈ sourceSieveCarrier N (d * l.prod)
    (d * (l.take (l.length - 2)).prod * N) (l.getD (l.length - 2) 0) at hsource
  obtain ⟨hrange, hprime, _, _⟩ := mem_filter.mp hsource
  exact omega3_prime_output_lt hN he hprime (Nat.lt_succ_iff.mp (mem_range.mp hrange))

/-- The precise repeated-divisibility event uses the complete original
labelled divisor, rather than only the square prime. -/
theorem collision_complement_mem {N d ell : ℕ} {l : List ℕ}
    (hN : 4 ≤ N) (he : Even N) (hfull : 0 < d * l.prod)
    (hell : ell ∈ collisionCarrier N d l) :
    N - ell ∈ omega3BadComplements N (d * l.prod) := by
  obtain ⟨hsource, r, hr, hrpre, _, hrres⟩ := mem_filter.mp hell
  change ell ∈ sourceSieveCarrier N (d * l.prod)
    (d * (l.take (l.length - 2)).prod * N) (l.getD (l.length - 2) 0) at hsource
  have hdiv := (mem_filter.mp hsource).2.2.1
  have hrf := hrpre.trans (take_prod_dvd_complete d l)
  have hrmem : r ∈ (d * l.prod).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hrf, hfull.ne'⟩
  have hpositive := Nat.sub_pos_of_lt (collision_output_lt hN he hell)
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le N ell)),
    hpositive.ne', r, hrmem, (Nat.dvd_div_iff_mul_dvd hdiv).mp hrres⟩

/-- Complementation is injective on the actual prime-index carrier. -/
theorem collision_card_le_bad_complements {N d : ℕ} {l : List ℕ}
    (hN : 4 ≤ N) (he : Even N) (hfull : 0 < d * l.prod) :
    (collisionCarrier N d l).card ≤ (omega3BadComplements N (d * l.prod)).card := by
  apply card_le_card_of_injOn (fun ell => N - ell)
  · intro ell hell
    exact collision_complement_mem hN he hfull hell
  · intro ell hell ell' hell' heq
    have hlt := collision_output_lt hN he hell
    have hlt' := collision_output_lt hN he hell'
    omega

/-- Exact finite floor count, retaining the complete labelled product. -/
theorem collision_card_le_floor_sum {N d : ℕ} {l : List ℕ}
    (hN : 4 ≤ N) (he : Even N) (hfull : 0 < d * l.prod) :
    (collisionCarrier N d l).card ≤
      ∑ r ∈ (d * l.prod).primeFactors, N / ((d * l.prod) * r) :=
  (collision_card_le_bad_complements hN he hfull).trans
    (omega3_bad_complements_card_le N (d * l.prod))

/-- A tuple whose complete divisor exceeds N contributes no collision. -/
theorem collision_empty_of_full_gt {N d : ℕ} {l : List ℕ}
    (hN : 4 ≤ N) (he : Even N) (hlarge : N < d * l.prod) :
    collisionCarrier N d l = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ell hell
  have hsource := (mem_filter.mp hell).1
  change ell ∈ sourceSieveCarrier N (d * l.prod)
    (d * (l.take (l.length - 2)).prod * N) (l.getD (l.length - 2) 0) at hsource
  have hdiv := (mem_filter.mp hsource).2.2.1
  have hpositive := Nat.sub_pos_of_lt (collision_output_lt hN he hell)
  have hbound := (Nat.le_of_dvd hpositive hdiv).trans (Nat.sub_le N ell)
  omega

/-- The genuine fixed-positive-cutoff power estimate for one labelled
collision carrier. No size premise is imposed on tuples that are empty. -/
theorem collision_card_le_power {N d : ℕ} {l : List ℕ} {eta : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hfull : 0 < d * l.prod) (heta : 0 < eta)
    (hrough : ∀ r ∈ (d * l.prod).primeFactors, (N : ℝ) ^ eta ≤ (r : ℝ)) :
    ((collisionCarrier N d l).card : ℝ) ≤
      (1 / eta) * (N : ℝ) / (((d * l.prod : ℕ) : ℝ) * (N : ℝ) ^ eta) := by
  by_cases hsize : d * l.prod ≤ N
  · calc
      ((collisionCarrier N d l).card : ℝ) ≤
          ∑ r ∈ (d * l.prod).primeFactors, ((N / ((d * l.prod) * r) : ℕ) : ℝ) := by
        exact_mod_cast collision_card_le_floor_sum hN he hfull
      _ ≤ _ := omega3_bad_floor_sum_le (by omega : 1 < N) hfull hsize heta hrough
  · rw [collision_empty_of_full_gt hN he (Nat.lt_of_not_ge hsize), card_empty, Nat.cast_zero]
    exact div_nonneg (mul_nonneg (one_div_nonneg.mpr heta.le) (Nat.cast_nonneg N))
      (mul_nonneg (Nat.cast_nonneg (d * l.prod)) (Real.rpow_nonneg (Nat.cast_nonneg N) eta))

end
end ImbalancedChen.P2EnhancedCollisionFloorBound
