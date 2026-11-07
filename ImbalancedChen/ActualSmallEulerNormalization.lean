import ImbalancedChen.RosserEndpointBridge
import ImbalancedChen.EulerNormalizationLimit
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# A uniform upper normalization for the actual small Euler product

The real prime cutoff is strict. Its ordinary Mertens product is therefore
the inclusive product at `Nat.ceil w - 1`, including when `w` is an integer.
We use the proved order bound for that product and a finite upper comparison
with the manuscript's own singular series. No convergence of an omitted
target-prime tail is needed.

The final constant is uniform in the positive even target and the enumeration
cap, provided the cap contains every prime below `w`. The target zero is
excluded because its totalized finite prime-divisor correction is not the
correction over all prime divisors of zero. This is an upper bound, not the
sharp Mertens normalization or a fixed-coordinate raw Rosser density limit.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The actual Euler product has precisely the existing strict natural
cap `ceil w`, without introducing a prime equal to the real cutoff. -/
theorem actualSmallEulerProduct_eq_finiteSieveDensity
    (N cap : ℕ) (w : ℝ) (hwcap : w ≤ (cap : ℝ)) :
    actualSmallEulerProduct N cap w = finiteSieveDensity N (Nat.ceil w) := by
  unfold actualSmallEulerProduct finiteSieveDensity
  rw [actualSmallPrimeFinset_eq_goldbachB10SiftingPrimes N cap w hwcap]
  rfl

/-- A strict natural prime cap is the inclusive Mertens product at its
predecessor. The subtraction is in naturals and the endpoint is explicit. -/
theorem primeEulerProduct_eq_mertensPrimeProduct_pred {z : ℕ} (hz : 1 ≤ z) :
    primeEulerProduct z =
      MathlibNt.SieveTheory.MertensTheorem.primeProduct (z - 1) := by
  unfold primeEulerProduct primesBelowCap MathlibNt.SieveTheory.MertensTheorem.primeProduct
  rw [Nat.sub_add_cancel hz]

/-- Every finite odd-prime constant product is at most one. Only finite
factor inequalities are used, not convergence of the infinite product. -/
theorem oddEulerProduct_le_one (z : ℕ) : oddEulerProduct z ≤ 1 := by
  unfold oddEulerProduct
  apply Finset.prod_le_one
  · intro p hp
    have hpData := mem_oddPrimesBelowCap.mp hp
    exact (oddPrimeFactor_pos ⟨p, hpData.2.1, hpData.2.2⟩).le
  · intro p _hp
    exact sub_le_self _ (by positivity)

/-- The below-cap target correction is bounded by the full correction,
since every factor in its complementary tail is at least one. -/
theorem centerPrimeCorrectionBelowCap_le_full {N : ℕ} (hN : N ≠ 0) (z : ℕ) :
    centerPrimeCorrectionBelowCap N z ≤ centerPrimeCorrection N := by
  calc
    centerPrimeCorrectionBelowCap N z = centerPrimeCorrectionBelowCap N z * 1 :=
      (mul_one _).symm
    _ ≤ centerPrimeCorrectionBelowCap N z * centerPrimeTailCorrection N z :=
      mul_le_mul_of_nonneg_left (one_le_centerPrimeTailCorrection N z)
        (centerPrimeCorrectionBelowCap_pos N z).le
    _ = centerPrimeCorrection N := (centerPrimeCorrection_eq_below_mul_tail hN).symm

/-- A coarse but uniform comparison with the manuscript's singular series.
The factor two is retained from the exact finite Euler factorization. -/
theorem finiteSieveDensity_le_primeEulerProduct_singularSeries
    {N z : ℕ} (hN : N ≠ 0) (hEven : Even N) (hz : 2 < z) :
    finiteSieveDensity N z ≤
      (2 / twinPrimeConstant) * primeEulerProduct z * singularSeries N := by
  have hproduct : oddEulerProduct z * centerPrimeCorrectionBelowCap N z ≤
      centerPrimeCorrection N := by
    simpa only [one_mul] using
      mul_le_mul (oddEulerProduct_le_one z) (centerPrimeCorrectionBelowCap_le_full hN z)
        (centerPrimeCorrectionBelowCap_pos N z).le (by norm_num : (0 : ℝ) ≤ 1)
  calc
    finiteSieveDensity N z =
        2 * primeEulerProduct z *
          (oddEulerProduct z * centerPrimeCorrectionBelowCap N z) := by
      rw [finiteSieveDensity_euler_identity hEven hz]
      change 2 * primeEulerProduct z * oddEulerProduct z *
        centerPrimeCorrectionBelowCap N z = _
      ring
    _ ≤ 2 * primeEulerProduct z * centerPrimeCorrection N :=
      mul_le_mul_of_nonneg_left hproduct
        (mul_nonneg (by norm_num) (primeEulerProduct_pos z).le)
    _ = (2 / twinPrimeConstant) * primeEulerProduct z * singularSeries N := by
      change _ = (2 / twinPrimeConstant) * primeEulerProduct z *
        (twinPrimeConstant * centerPrimeCorrection N)
      field_simp [twinPrimeConstant_pos.ne']

/-- One positive Mertens constant bounds the ordinary prime product at
every real strict cutoff at least four. The analytic input is the proved
order theorem at the inclusive natural endpoint `ceil w - 1`. -/
theorem exists_primeEulerProduct_natCeil_le_log :
    ∃ A : ℝ, 0 < A ∧ ∀ w : ℝ, 4 ≤ w →
      primeEulerProduct (Nat.ceil w) ≤ A / Real.log w := by
  obtain ⟨c₁, c₂, _hc₁, hbound⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.primeProduct_asymptotic_order
  let A : ℝ := max c₂ 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨2 * A, mul_pos (by norm_num) hA, ?_⟩
  intro w hw
  have hzFour : 4 ≤ Nat.ceil w := by
    exact_mod_cast hw.trans (Nat.le_ceil w)
  have hxTwo : 2 ≤ Nat.ceil w - 1 := by omega
  have hxCast : ((Nat.ceil w - 1 : ℕ) : ℝ) = (Nat.ceil w : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil w), Nat.cast_one]
  have hxLower : w - 1 ≤ ((Nat.ceil w - 1 : ℕ) : ℝ) := by
    rw [hxCast]
    linarith [Nat.le_ceil w]
  have hxPos : 0 < ((Nat.ceil w - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Nat.ceil w - 1 by omega)
  have hlogx : 0 < Real.log ((Nat.ceil w - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Nat.ceil w - 1 by omega))
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hsquare : w ≤ (((Nat.ceil w - 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (((Nat.ceil w - 1 : ℕ) : ℝ) - 1)]
  have hlogCompare : Real.log w ≤ 2 * Real.log ((Nat.ceil w - 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by linarith : 0 < w) hsquare
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  rw [primeEulerProduct_eq_mertensPrimeProduct_pred (by omega : 1 ≤ Nat.ceil w)]
  calc
    MathlibNt.SieveTheory.MertensTheorem.primeProduct (Nat.ceil w - 1) ≤
        c₂ / Real.log ((Nat.ceil w - 1 : ℕ) : ℝ) := (hbound _ hxTwo).2
    _ ≤ A / Real.log ((Nat.ceil w - 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (le_max_left _ _) hlogx.le
    _ ≤ (2 * A) / Real.log w := by
      apply (div_le_div_iff₀ hlogx hlogw).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlogCompare hA.le]

/-- Uniform upper normalization of the actual full small-prime Euler
product. All constants precede the positive even target and finite cap.
No tail asymptotic or sieve-density hypothesis is supplied by the caller. -/
theorem exists_actualSmallEulerProduct_le_singularSeries_log :
    ∃ B : ℝ, 0 < B ∧ ∀ N cap : ℕ, 0 < N → Even N →
      ∀ w : ℝ, 4 ≤ w → w ≤ (cap : ℝ) →
        actualSmallEulerProduct N cap w ≤ B * singularSeries N / Real.log w := by
  obtain ⟨A, hA, hbound⟩ := exists_primeEulerProduct_natCeil_le_log
  let B : ℝ := 2 * A / twinPrimeConstant
  have hB : 0 < B := div_pos (mul_pos (by norm_num) hA) twinPrimeConstant_pos
  refine ⟨B, hB, ?_⟩
  intro N cap hN hEven w hw hwcap
  have hz : 2 < Nat.ceil w := by
    have hfour : 4 ≤ Nat.ceil w := by exact_mod_cast hw.trans (Nat.le_ceil w)
    omega
  rw [actualSmallEulerProduct_eq_finiteSieveDensity N cap w hwcap]
  calc
    finiteSieveDensity N (Nat.ceil w) ≤
        (2 / twinPrimeConstant) * primeEulerProduct (Nat.ceil w) * singularSeries N :=
      finiteSieveDensity_le_primeEulerProduct_singularSeries (Nat.ne_of_gt hN) hEven hz
    _ ≤ (2 / twinPrimeConstant) * (A / Real.log w) * singularSeries N :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound w hw)
          (div_nonneg (by norm_num) twinPrimeConstant_pos.le))
        (singularSeries_pos N).le
    _ = B * singularSeries N / Real.log w := by dsimp [B]; ring

end

end ImbalancedChen
