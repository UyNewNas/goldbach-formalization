import ImbalancedChen.EulerNormalizationLimit
import ImbalancedChen.ChenInitialCorrectionBudget

/-!
# Uniform center-prime Euler tails at every fixed power cutoff

The real cutoff is strict in the small correction and inclusive in the
omitted tail. We reuse the existing exact finite correction identities at
`ceil z`, which has precisely these real endpoints. For `N > 0` and `z >= 4`,
the actual tail satisfies

`1 <= tail(N,z) <= exp(2 * log N / (z * log 2))`.

Each omitted local factor is at most `exp(2/z)`, and the number of omitted
primes is bounded by the proved logarithmic count of distinct prime factors
of `N`. This gives convergence to one for `z = N^a`, for every fixed real
`a > 0`, uniformly over all sufficiently large natural centers, hence also
over the even centers. The strict-small/full correction ratio has the same
limit. No Mertens estimate or asymptotic for the entire sieve density is
assumed or claimed. The finite upper bound explicitly excludes `N = 0`.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators

/-- The omitted correction for the literal real cutoff. Equality with the
cutoff belongs to this tail, through the exact natural ceiling. -/
def centerEulerTail (N : ℕ) (z : ℝ) : ℝ :=
  centerPrimeTailCorrection N (Nat.ceil z)

/-- The strict real-cutoff part of the existing finite correction. At zero
it retains the below-cap divisibility convention of `FiniteSieveEuler`. -/
def centerEulerSmallCorrection (N : ℕ) (z : ℝ) : ℝ :=
  centerPrimeCorrectionBelowCap N (Nat.ceil z)

/-- The tail is a product over actual odd prime divisors with real `p >= z`.
At zero this uses the existing empty prime-factor convention. -/
theorem centerEulerTail_eq_real_product (N : ℕ) (z : ℝ) :
    centerEulerTail N z =
      ∏ p ∈ (oddPrimeDivisors N).filter (fun p : ℕ => z ≤ (p : ℝ)),
        ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  unfold centerEulerTail centerPrimeTailCorrection oddPrimeDivisorsTail
  simp only [Nat.ceil_le]

/-- Below the real cutoff means strictly below, including at integer
endpoints. The full prime-divisor representation requires `N != 0`. -/
theorem centerEulerSmallCorrection_eq_real_product {N : ℕ} (hN : N ≠ 0)
    (z : ℝ) :
    centerEulerSmallCorrection N z =
      ∏ p ∈ (oddPrimeDivisors N).filter (fun p : ℕ => (p : ℝ) < z),
        ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  unfold centerEulerSmallCorrection centerPrimeCorrectionBelowCap
  rw [oddPrimeDivisorsBelowCap_eq_filter hN]
  simp only [Nat.lt_ceil]

/-- The existing exact finite split, now with the literal real cutoff.
There is no new Euler-product identity or asymptotic premise here. -/
theorem centerPrimeCorrection_eq_small_mul_centerEulerTail
    {N : ℕ} (hN : N ≠ 0) (z : ℝ) :
    centerPrimeCorrection N = centerEulerSmallCorrection N z * centerEulerTail N z :=
  centerPrimeCorrection_eq_below_mul_tail (z := Nat.ceil z) hN

theorem one_le_centerEulerTail (N : ℕ) (z : ℝ) :
    1 ≤ centerEulerTail N z :=
  one_le_centerPrimeTailCorrection N (Nat.ceil z)

/-- Explicit uniform control using the genuine distinct-prime count.
The hypotheses keep the logarithmic count and all denominators valid. -/
theorem centerEulerTail_bounds {N : ℕ} {z : ℝ}
    (hN : 0 < N) (hz : 4 ≤ z) :
    1 ≤ centerEulerTail N z ∧
      centerEulerTail N z ≤ Real.exp (2 * Real.log (N : ℝ) / (z * Real.log 2)) := by
  classical
  refine ⟨one_le_centerEulerTail N z, ?_⟩
  have hzpos : 0 < z := by linarith
  let S := (oddPrimeDivisors N).filter (fun p : ℕ => z ≤ (p : ℝ))
  have hsub : S ⊆ N.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hcard : (S.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have hle : (S.card : ℝ) ≤ (N.primeFactors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hle.trans (chen_primeFactors_card_le_log hN)
  rw [centerEulerTail_eq_real_product]
  change (∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤ _
  calc
    (∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤
        ∏ _p ∈ S, Real.exp (2 / z) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact zero_le_one.trans (one_le_centerPrimeFactor
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
      · intro p hp
        have hpz : z ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2
        have hppos : 0 < (p : ℝ) - 2 := by linarith
        have hfactor : ((p : ℝ) - 1) / ((p : ℝ) - 2) =
            1 + 1 / ((p : ℝ) - 2) := by
          field_simp [hppos.ne'] <;> ring
        have hrecip : 1 / ((p : ℝ) - 2) ≤ 2 / z := by
          apply (div_le_div_iff₀ hppos hzpos).mpr
          linarith
        calc
          ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + 1 / ((p : ℝ) - 2) := hfactor
          _ ≤ 1 + 2 / z := add_le_add_left hrecip 1
          _ ≤ Real.exp (2 / z) := by
            simpa only [add_comm] using Real.add_one_le_exp (2 / z)
    _ = Real.exp ((S.card : ℝ) * (2 / z)) := by
      rw [← Real.exp_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp ((Real.log (N : ℝ) / Real.log 2) * (2 / z)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard
        (div_nonneg (by norm_num) hzpos.le))
    _ = Real.exp (2 * Real.log (N : ℝ) / (z * Real.log 2)) := by
      congr 1
      ring

/-- The actual strict-small/full correction ratio is the reciprocal of
the actual tail. This is the already proved finite ratio identity. -/
theorem centerEulerSmallCorrection_div_full_eq_inv_tail
    {N : ℕ} (hN : N ≠ 0) (z : ℝ) :
    centerEulerSmallCorrection N z / centerPrimeCorrection N =
      (centerEulerTail N z)⁻¹ :=
  centerPrimeCorrectionBelowCap_div_full_eq_inv_tail (z := Nat.ceil z) hN

/-- Every fixed positive real power cutoff suffices. The center varies
with the cutoff; this is not convergence at a fixed center. -/
theorem tendsto_centerEulerTail_power {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => centerEulerTail N ((N : ℝ) ^ a)) atTop (𝓝 1) := by
  have hdecay : Tendsto (fun N : ℕ =>
      2 * Real.log (N : ℝ) / ((N : ℝ) ^ a * Real.log 2)) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, zero_div, mul_div_assoc, div_div] using
      ((tendsto_nat_log_pow_div_rpow 1 ha).const_mul 2).div_const (Real.log 2)
  have hupper : Tendsto (fun N : ℕ =>
      Real.exp (2 * Real.log (N : ℝ) / ((N : ℝ) ^ a * Real.log 2)))
      atTop (𝓝 1) := by
    simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hdecay
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · exact Filter.Eventually.of_forall (fun N => one_le_centerEulerTail N ((N : ℝ) ^ a))
  · filter_upwards [hpower.eventually (eventually_ge_atTop (4 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with N hz hN
    exact (centerEulerTail_bounds (by omega : 0 < N) hz).2

/-- Truncating the genuine singular-series correction at any fixed
positive real power changes it by a ratio tending to one. -/
theorem tendsto_centerEulerSmallCorrection_div_full_power
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      centerEulerSmallCorrection N ((N : ℝ) ^ a) / centerPrimeCorrection N)
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun N : ℕ => (centerEulerTail N ((N : ℝ) ^ a))⁻¹)
      atTop (𝓝 1) := by
    simpa only [inv_one] using
      (tendsto_centerEulerTail_power ha).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (centerEulerSmallCorrection_div_full_eq_inv_tail
    (by omega : N ≠ 0) ((N : ℝ) ^ a)).symm

/-- One threshold works for every sufficiently large center, with both
the positivity/cutoff gates and the relative error explicit. In particular
the same threshold works after restricting the centers to even integers. -/
theorem exists_centerEulerTail_power_threshold {a : ℝ} (ha : 0 < a)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      0 < N ∧ 4 ≤ (N : ℝ) ^ a ∧
      |centerEulerTail N ((N : ℝ) ^ a) - 1| < epsilon ∧
      |centerEulerSmallCorrection N ((N : ℝ) ^ a) / centerPrimeCorrection N - 1| <
        epsilon := by
  have htail := Metric.tendsto_nhds.mp (tendsto_centerEulerTail_power ha) epsilon hepsilon
  have hratio := Metric.tendsto_nhds.mp
    (tendsto_centerEulerSmallCorrection_div_full_power ha) epsilon hepsilon
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [htail, hratio, hpower.eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with N ht hr hz hN
  exact ⟨by omega, hz, by simpa only [Real.dist_eq] using ht,
    by simpa only [Real.dist_eq] using hr⟩

end

end ImbalancedChen
