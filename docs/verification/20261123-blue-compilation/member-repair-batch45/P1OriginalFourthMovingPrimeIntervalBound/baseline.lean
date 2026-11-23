import ImbalancedChen.P1OriginalFourthSmallBinWeightedMass
import ImbalancedChen.RoughAbsoluteDensity

/-!
# A uniform moving-interval bound for the original fourth-prime bin

This source-only module extracts a finite reciprocal-prime interval estimate
from the pinned inverse-product theorem. Unlike a fixed-exponent Mertens
limit, its constant is independent of both endpoints and of the target.
Its box corollary applies directly to the preceding original-policy weighted
bin, including target-prime deletion and the original `19/96` cutoff.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open P1OriginalCoarseContinuation
open P1OriginalFourthSmallPrimeStratification
open P1OriginalFourthSmallBinWeightedMass

namespace P1OriginalFourthMovingPrimeIntervalBound

/-- The degree-zero and degree-one terms of the positive finite Euler
product. The proof does not invoke a prime-counting asymptotic. -/
private theorem one_add_reciprocal_sum_le_euler (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    1 + ∑ p ∈ S, 1 / ((p : ℝ) - 1) ≤
      ∏ p ∈ S, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (hprime p (Finset.mem_insert_self p S)).one_lt
    have hxp : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
    have hsum : 0 ≤ ∑ q ∈ S, 1 / ((q : ℝ) - 1) := by
      apply Finset.sum_nonneg
      intro q hq
      have hq1 : (1 : ℝ) < q := by
        exact_mod_cast (hprime q (Finset.mem_insert_of_mem hq)).one_lt
      positivity
    have hih : 1 + ∑ q ∈ S, 1 / ((q : ℝ) - 1) ≤
        ∏ q ∈ S, (1 + 1 / ((q : ℝ) - 1)) := by
      apply ih
      intro q hq
      exact hprime q (Finset.mem_insert_of_mem hq)
    rw [Finset.sum_insert hp, Finset.prod_insert hp]
    have hmul := mul_le_mul_of_nonneg_left hih (by linarith :
      0 ≤ 1 + 1 / ((p : ℝ) - 1))
    nlinarith [mul_nonneg hxp hsum]

/-- Uniform real-endpoint interval mass, valid when the last-prime
exponents move with `N`. The pinned constant precedes every target, cap,
and endpoint. The strict upper endpoint and target deletion are literal. -/
theorem exists_uniform_reciprocal_interval_bound :
    ∃ K : ℝ, 1 < K ∧ ∀ (N cap : ℕ), Even N →
      ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        (∑ p ∈ roughPrimeFinset N cap w z, 1 / ((p : ℝ) - 1)) ≤
          Real.log z / Real.log w * (1 + K / Real.log w) - 1 := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N cap hEven w z hw hwz
  let P := roughPrimeFinset N cap w z
  have hp : ∀ p ∈ P, Nat.Prime p ∧ 2 < p :=
    fun _ h => roughPrimeFinset_odd_of_even hEven h
  have hsum : 1 + ∑ p ∈ P, 1 / ((p : ℝ) - 1) ≤
      ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) :=
    one_add_reciprocal_sum_le_euler P (fun p h => (hp p h).1)
  have hprod := roughPrime_eulerProduct_le_inverseProduct N cap w z hEven
  have hM := hinterval P hp w z hw hwz
    (fun p h => (mem_roughPrimeFinset.mp h).2.2.2)
  change (∑ p ∈ P, 1 / ((p : ℝ) - 1)) ≤ _
  linarith [hsum.trans (hprod.trans hM)]

/-- The same theorem on a target-dependent power interval. There is no
fixed-exponent premise, so the lower exponent may move toward zero. -/
theorem actualPrimeReciprocalMass_le_moving_ratio
    (K : ℝ)
    (hK : ∀ (N cap : ℕ), Even N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      (∑ p ∈ roughPrimeFinset N cap w z, 1 / ((p : ℝ) - 1)) ≤
        Real.log z / Real.log w * (1 + K / Real.log w) - 1)
    (N : ℕ) (hEven : Even N) (lo hi : ℝ)
    (hlo : 2 ≤ (N : ℝ) ^ lo) (hlohi : lo ≤ hi) (hN : 1 < N) :
    actualPrimeReciprocalMass N lo hi ≤
      Real.log ((N : ℝ) ^ hi) / Real.log ((N : ℝ) ^ lo) *
        (1 + K / Real.log ((N : ℝ) ^ lo)) - 1 := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hwz : (N : ℝ) ^ lo ≤ (N : ℝ) ^ hi :=
    Real.rpow_le_rpow_of_exponent_le hn.le hlohi
  exact hK N (Nat.ceil ((N : ℝ) ^ hi)) hEven _ _ hlo hwz

/-- The terminal coordinate of a reciprocal bin has a summable main term
and a target-uniform `1/log N` error. This holds for moving `r`; there is
no fixed-exponent Mertens limit in the proof. -/
theorem weighted_last_prime_interval_le_terms
    (K : ℝ) (hKpos : 0 ≤ K)
    (hK : ∀ (N cap : ℕ), Even N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      (∑ p ∈ roughPrimeFinset N cap w z, 1 / ((p : ℝ) - 1)) ≤
        Real.log z / Real.log w * (1 + K / Real.log w) - 1)
    (N : ℕ) (hN : 1 < N) (hEven : Even N)
    (a : ℝ) (ha : 0 < a) (r : ℕ) (hr : 1 ≤ r)
    (hlo : 2 ≤ (N : ℝ) ^ (a / ((r : ℝ) + 1))) :
    (a / (r : ℝ)) * actualPrimeReciprocalMass N
        (a / ((r : ℝ) + 1))
        (a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1))) ≤
      2 * a / (r : ℝ) ^ 2 + 6 * K / Real.log (N : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlohi : a / ((r : ℝ) + 1) ≤
      a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1)) := by
    have hsmall : a / ((r : ℝ) + 1) ≤ a / (r : ℝ) :=
      div_le_div_of_nonneg_left ha.le hrR (by linarith)
    have hextra : 0 ≤ a / ((r : ℝ) * ((r : ℝ) + 1)) := by positivity
    linarith
  have hwin := actualPrimeReciprocalMass_le_moving_ratio K hK N hEven
    (a / ((r : ℝ) + 1))
    (a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1)))
    hlo hlohi hN
  have hEq :
      (a / (r : ℝ)) *
        (Real.log ((N : ℝ) ^
            (a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1)))) /
            Real.log ((N : ℝ) ^ (a / ((r : ℝ) + 1))) *
          (1 + K / Real.log ((N : ℝ) ^ (a / ((r : ℝ) + 1)))) - 1) =
        2 * a / (r : ℝ) ^ 2 +
          K * ((r : ℝ) + 2) * ((r : ℝ) + 1) /
            ((r : ℝ) ^ 2 * Real.log (N : ℝ)) := by
    rw [Real.log_rpow hNpos, Real.log_rpow hNpos]
    field_simp [hrR.ne', hr1.ne', ha.ne', hlogN.ne']
    ring
  have hpoly : ((r : ℝ) + 2) * ((r : ℝ) + 1) ≤ 6 * (r : ℝ) ^ 2 := by
    have hrone : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hnum : K * ((r : ℝ) + 2) * ((r : ℝ) + 1) ≤
      6 * K * (r : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hpoly hKpos]
  have hden : 0 ≤ (r : ℝ) ^ 2 * Real.log (N : ℝ) := by positivity
  have herr : K * ((r : ℝ) + 2) * ((r : ℝ) + 1) /
      ((r : ℝ) ^ 2 * Real.log (N : ℝ)) ≤
        6 * K / Real.log (N : ℝ) := by
    have h := div_le_div_of_nonneg_right hnum hden
    convert h using 1 <;> field_simp [hrR.ne', hlogN.ne'] <;> ring
  calc
    _ ≤ (a / (r : ℝ)) *
        (Real.log ((N : ℝ) ^
            (a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1)))) /
            Real.log ((N : ℝ) ^ (a / ((r : ℝ) + 1))) *
          (1 + K / Real.log ((N : ℝ) ^ (a / ((r : ℝ) + 1)))) - 1) :=
      mul_le_mul_of_nonneg_left hwin (div_nonneg ha.le hrR.le)
    _ = 2 * a / (r : ℝ) ^ 2 +
        K * ((r : ℝ) + 2) * ((r : ℝ) + 1) /
          ((r : ℝ) ^ 2 * Real.log (N : ℝ)) := hEq
    _ ≤ 2 * a / (r : ℝ) ^ 2 + 6 * K / Real.log (N : ℝ) := add_le_add_left herr _

/-- A moving-endpoint, target-uniform envelope for each exact original
bin. It is conditional only on explicit geometric endpoint inequalities
needed by the pinned interval theorem, not on a small-remainder supplier. -/
theorem weightedBinMass_le_uniform_ratio_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ) (ha : 0 < a)
    (J4 : Finset (FourthCell m)) (N cap : ℕ) (hN : 1 < N)
    (hEven : Even N) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (k : Bin) (K : ℝ)
    (hK : ∀ (N cap : ℕ), Even N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      (∑ p ∈ roughPrimeFinset N cap w z, 1 / ((p : ℝ) - 1)) ≤
        Real.log z / Real.log w * (1 + K / Real.log w) - 1)
    (hlow : ∀ i : Fin 4, 2 ≤ (N : ℝ) ^ (binLo omega a k.1 i))
    (horder : ∀ i : Fin 4, binLo omega a k.1 i ≤ binHi a k.1 i) :
    weightedBinMass e chi m omega a old new N cap j k ≤
      (a / (k.1 : ℝ)) *
        ∏ i : Fin 4,
          (Real.log ((N : ℝ) ^ (binHi a k.1 i)) /
                Real.log ((N : ℝ) ^ (binLo omega a k.1 i)) *
              (1 + K / Real.log ((N : ℝ) ^ (binLo omega a k.1 i))) - 1) := by
  have hbox := weightedBinMass_le_prime_box e chi m omega a old new ha J4
    N cap hN j hj k
  have hfac (i : Fin 4) :
      actualPrimeReciprocalMass N (binLo omega a k.1 i) (binHi a k.1 i) ≤
        Real.log ((N : ℝ) ^ (binHi a k.1 i)) /
          Real.log ((N : ℝ) ^ (binLo omega a k.1 i)) *
          (1 + K / Real.log ((N : ℝ) ^ (binLo omega a k.1 i))) - 1 :=
    actualPrimeReciprocalMass_le_moving_ratio K hK N hEven _ _
      (hlow i) (horder i) hN
  have hfac0 (i : Fin 4) :
      0 ≤ actualPrimeReciprocalMass N (binLo omega a k.1 i) (binHi a k.1 i) := by
    unfold actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    positivity
  have hfacR (i : Fin 4) : 0 ≤
        Real.log ((N : ℝ) ^ (binHi a k.1 i)) /
          Real.log ((N : ℝ) ^ (binLo omega a k.1 i)) *
          (1 + K / Real.log ((N : ℝ) ^ (binLo omega a k.1 i))) - 1 :=
    (hfac0 i).trans (hfac i)
  have hprod :
      (∏ i : Fin 4, actualPrimeReciprocalMass N
        (binLo omega a k.1 i) (binHi a k.1 i)) ≤
        ∏ i : Fin 4,
          (Real.log ((N : ℝ) ^ (binHi a k.1 i)) /
                Real.log ((N : ℝ) ^ (binLo omega a k.1 i)) *
              (1 + K / Real.log ((N : ℝ) ^ (binLo omega a k.1 i))) - 1) := by
    apply Finset.prod_le_prod
    · intro i _
      exact hfac0 i
    · intro i _
      exact hfac i
  exact hbox.trans (mul_le_mul_of_nonneg_left hprod
    (div_nonneg ha.le (Nat.cast_nonneg _)))

/-- Closed supplier-free form: the same pinned interval constant works for
every original-policy bin and every even target, including moving k. -/
theorem exists_weightedBinMass_uniform_ratio_box :
    ∃ K : ℝ, 1 < K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ), 0 < a →
      ∀ (J4 : Finset (FourthCell m)) (N cap : ℕ), 1 < N → Even N →
      ∀ (j : FourthCell m), j ∈ selectedFourthCells e chi m omega J4 →
      ∀ (k : Bin),
        (∀ i : Fin 4, 2 ≤ (N : ℝ) ^ (binLo omega a k.1 i)) →
        (∀ i : Fin 4, binLo omega a k.1 i ≤ binHi a k.1 i) →
        weightedBinMass e chi m omega a old new N cap j k ≤
          (a / (k.1 : ℝ)) *
            ∏ i : Fin 4,
              (Real.log ((N : ℝ) ^ (binHi a k.1 i)) /
                    Real.log ((N : ℝ) ^ (binLo omega a k.1 i)) *
                  (1 + K / Real.log ((N : ℝ) ^ (binLo omega a k.1 i))) - 1) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_reciprocal_interval_bound
  refine ⟨K, hK, ?_⟩
  intro e chi m omega a old new ha J4 N cap hN hEven j hj k hlow horder
  exact weightedBinMass_le_uniform_ratio_box e chi m omega a old new ha J4
    N cap hN hEven j hj k K hbound hlow horder

end P1OriginalFourthMovingPrimeIntervalBound

end

end ImbalancedChen
