import ImbalancedChen.RealHalfProductSource
import ImbalancedChen.HalfProductMassLimit

/-!
# The arbitrary-real half-product mass coefficient

The current theorem quantifies over every real `b` with `1 / 2 < b < 1`,
whereas the earlier half-product mass module is indexed by a rational pair
`num / den`.  This file isolates the exact real exponent geometry needed by
the weighted-prime Mertens step.

For `alpha = b / (1 + b)` and `beta = 1 / (1 + b)`, the high-prime window is
`N^alpha < r <= sqrt N`, and the fixed-test integral is exactly
`log (1 / b)`.  The final theorem below deliberately takes the standard
weighted-prime integral limit as an explicit premise.  It proves that this
upstream Mertens conclusion has exactly the manuscript's coefficient; it does
not assume a half-product cardinality or the desired bad-count estimate.
-/

namespace ImbalancedChen

noncomputable section

open Filter MeasureTheory Topology
open scoped BigOperators

/-- Lower logarithmic exponent for the arbitrary-real bad semiprime mass. -/
def realHalfProductMassAlpha (b : ℝ) : ℝ := b / (1 + b)

/-- Complementary exponent controlling the low-prime rectangle. -/
def realHalfProductMassBeta (b : ℝ) : ℝ := 1 / (1 + b)

/-- Exact exponent geometry for every manuscript parameter `0 < b < 1`. -/
theorem realHalfProductMass_exponents {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    0 < realHalfProductMassAlpha b ∧
      realHalfProductMassAlpha b < 1 / 2 ∧
      0 < realHalfProductMassBeta b ∧
      realHalfProductMassAlpha b < realHalfProductMassBeta b ∧
      realHalfProductMassAlpha b + realHalfProductMassBeta b = 1 := by
  have hs : 0 < 1 + b := by linarith
  unfold realHalfProductMassAlpha realHalfProductMassBeta
  refine ⟨div_pos hb hs, ?_, div_pos zero_lt_one hs, ?_, ?_⟩
  · apply (div_lt_iff₀ hs).mpr
    nlinarith
  · exact (div_lt_div_iff_of_pos_right hs).mpr hb1
  · rw [← add_div, add_comm, div_self (ne_of_gt hs)]

/-- The two exponents have the ratio which appears in the manuscript's
ordered bad-semiprime mass. -/
theorem realHalfProductMass_beta_div_alpha {b : ℝ} (hb : 0 < b) :
    realHalfProductMassBeta b / realHalfProductMassAlpha b = 1 / b := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hs : 1 + b ≠ 0 := by linarith
  unfold realHalfProductMassAlpha realHalfProductMassBeta
  field_simp [hb0, hs]

/-- Algebraic form used to transfer the strict badness wall between the two
prime variables. -/
theorem realHalfProductMass_alpha_eq_mul_beta {b : ℝ} :
    realHalfProductMassAlpha b = b * realHalfProductMassBeta b := by
  unfold realHalfProductMassAlpha realHalfProductMassBeta
  ring

/-- Below the exact split, the strict badness condition forces the larger
prime below the complementary power.  This is the real-exponent counterpart
of `halfProduct_low_prime_lt_power`. -/
theorem realHalfProduct_low_prime_lt_power {b : ℝ} (hb : 0 < b)
    {N r q : ℕ} (hN : 0 < N) (hr : 0 < r) (hq : 0 < q)
    (hrlow : (r : ℝ) ≤ (N : ℝ) ^ realHalfProductMassAlpha b)
    (hbad : (q : ℝ) ^ b < (r : ℝ)) :
    (q : ℝ) < (N : ℝ) ^ realHalfProductMassBeta b := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hlogBad : b * Real.log (q : ℝ) < Real.log (r : ℝ) := by
    have h := (Real.log_lt_log_iff (Real.rpow_pos_of_pos hqR b) hrR).mpr hbad
    simpa only [Real.log_rpow hqR] using h
  have hlogLow : Real.log (r : ℝ) ≤
      realHalfProductMassAlpha b * Real.log (N : ℝ) := by
    have h := Real.log_le_log hrR hrlow
    simpa only [Real.log_rpow hNR] using h
  have hlogTarget : Real.log (q : ℝ) <
      realHalfProductMassBeta b * Real.log (N : ℝ) := by
    rw [realHalfProductMass_alpha_eq_mul_beta] at hlogLow
    nlinarith
  apply (Real.log_lt_log_iff hqR
    (Real.rpow_pos_of_pos hNR (realHalfProductMassBeta b))).mp
  simpa only [Real.log_rpow hNR] using hlogTarget

/-- Above the exact split, the product bound alone makes the strict badness
condition automatic.  No primality or ordering is used. -/
theorem realHalfProduct_high_prime_bad {b : ℝ} (hb : 0 < b)
    {N r q : ℕ} (hr : 0 < r) (hq : 0 < q) (hprod : r * q ≤ N)
    (hlarge : (N : ℝ) ^ realHalfProductMassAlpha b < (r : ℝ)) :
    (q : ℝ) ^ b < (r : ℝ) := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hNR : (0 : ℝ) < N :=
    Nat.cast_pos.mpr ((Nat.mul_pos hr hq).trans_le hprod)
  have hs : 0 < 1 + b := by linarith
  have hprodR : (r : ℝ) * (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hprod
  have hlogProd : Real.log (r : ℝ) + Real.log (q : ℝ) ≤
      Real.log (N : ℝ) := by
    have h := Real.log_le_log (mul_pos hrR hqR) hprodR
    simpa only [Real.log_mul (ne_of_gt hrR) (ne_of_gt hqR)] using h
  have hlogLarge : b * Real.log (N : ℝ) <
      Real.log (r : ℝ) * (1 + b) := by
    have h := (Real.log_lt_log_iff
      (Real.rpow_pos_of_pos hNR (realHalfProductMassAlpha b)) hrR).mpr hlarge
    rw [Real.log_rpow hNR, realHalfProductMassAlpha, div_mul_eq_mul_div] at h
    exact (div_lt_iff₀ hs).mp h
  have hlogPow : Real.log ((q : ℝ) ^ b) < Real.log (r : ℝ) := by
    rw [Real.log_rpow hqR]
    nlinarith [mul_le_mul_of_nonneg_left hlogProd hb.le]
  exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos hqR b) hrR).mp hlogPow

/-- The fixed-test integral on the actual arbitrary-real high-prime window
is the claimed ordered mass `J_b = log (1 / b)`. -/
theorem realHalfProductMass_integral {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ u in realHalfProductMassAlpha b..(1 / 2 : ℝ),
        (1 / (1 - u)) / u) = Real.log (1 / b) := by
  simpa only [realHalfProductMassAlpha] using massLogIntegral_at_balanceRatio hb hb1

/-- Literal fixed-test reciprocal-prime sum for an arbitrary real exponent.
The lower endpoint is strict and the square-root endpoint is inclusive. -/
def realHalfProductMassWeightedPrimeSum (b : ℝ) (N : ℕ) : ℝ :=
  ∑ r ∈ halfProductHighPrimes N
      (Nat.floor ((N : ℝ) ^ realHalfProductMassAlpha b)),
    (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)

/-- Repository-local spelling of the standard weighted reciprocal-prime
logarithmic interval.  It is kept independent of any external package so an
audited supplier can later be connected by a small equality adapter. -/
def realPrimeReciprocalLogIntervalSum
    (f : ℝ → ℝ) (N : ℕ) (a c : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc (Nat.floor ((N : ℝ) ^ a))
      (Nat.floor ((N : ℝ) ^ c))).filter Nat.Prime,
    f (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)

/-- The literal manuscript high-prime sum is exactly the standard strict-left,
inclusive-right logarithmic interval specialization. -/
theorem realHalfProductMassWeightedPrimeSum_eq_interval (b : ℝ) (N : ℕ) :
    realHalfProductMassWeightedPrimeSum b N =
      realPrimeReciprocalLogIntervalSum (fun u => 1 / (1 - u)) N
        (realHalfProductMassAlpha b) (1 / 2) := by
  unfold realHalfProductMassWeightedPrimeSum realPrimeReciprocalLogIntervalSum
  apply Finset.sum_congr
  · ext r
    simp only [halfProductHighPrimes, Finset.mem_filter, Nat.mem_primesLE,
      Finset.mem_Ioc]
    rw [← Real.sqrt_eq_rpow, Real.nat_floor_real_sqrt_eq_nat_sqrt]
    aesop
  · intro r hr
    rfl

/-- Specializing a standard weighted-prime Mertens theorem to the manuscript
window gives the exact coefficient `log (1 / b)`.  The premise ends at the
independently proved integral, rather than restating the desired coefficient. -/
theorem tendsto_realHalfProductMassWeightedPrimeSum_of_integral_limit
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hMertens : Tendsto (fun N : ℕ =>
      realPrimeReciprocalLogIntervalSum (fun u => 1 / (1 - u)) N
        (realHalfProductMassAlpha b) (1 / 2)) atTop
      (𝓝 (∫ u in realHalfProductMassAlpha b..(1 / 2 : ℝ),
        (1 / (1 - u)) / u))) :
    Tendsto (realHalfProductMassWeightedPrimeSum b) atTop
      (𝓝 (Real.log (1 / b))) := by
  simpa only [← realHalfProductMassWeightedPrimeSum_eq_interval,
    realHalfProductMass_integral hb hb1] using hMertens

/-- The real exponent definition agrees exactly with the existing rational
mass module, so its already-proved finite/PNT machinery remains reusable at
rational parameters. -/
theorem realHalfProductMassAlpha_rat {num den : ℕ} (hden : 0 < den) :
    realHalfProductMassAlpha ((num : ℝ) / den) =
      halfProductMassAlpha num den := by
  have hd : (den : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hden)
  unfold realHalfProductMassAlpha halfProductMassAlpha
  field_simp [hd]
  ring

theorem realHalfProductMassBeta_rat {num den : ℕ} (hden : 0 < den) :
    realHalfProductMassBeta ((num : ℝ) / den) =
      halfProductMassBeta num den := by
  have hd : (den : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hden)
  unfold realHalfProductMassBeta halfProductMassBeta
  field_simp [hd]
  ring

/-- At positive-denominator rational parameters, the new literal sum is
definitionally the one consumed by `HalfProductMassLimit`. -/
theorem realHalfProductMassWeightedPrimeSum_rat {num den N : ℕ}
    (hden : 0 < den) :
    realHalfProductMassWeightedPrimeSum ((num : ℝ) / den) N =
      halfProductMassWeightedPrimeSum num den N := by
  simp only [realHalfProductMassWeightedPrimeSum, halfProductMassWeightedPrimeSum,
    realHalfProductMassAlpha_rat hden]

end

end ImbalancedChen
