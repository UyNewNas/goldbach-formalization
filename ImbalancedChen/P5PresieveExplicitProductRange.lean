import ImbalancedChen.P5PresieveAutomaticPrefixGates
import Mathlib.NumberTheory.Chebyshev

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Explicit, target-uniform finite arithmetic ranges. The proved primorial
bound gives M <= 4^r whenever w <= r. Conversely the undeleted primorial
always divides N*M below w and cap. Thus a positive-power presieve must
also pass the displayed lower obstruction; it is not licensed by choosing
eta merely small and fixed. No sigma or target constant is changed.
-/

namespace ImbalancedChen.P5Z.PresieveGateRegime

noncomputable section
open scoped BigOperators

/-- A proved exponential envelope for the ACTUAL deleted small product.
The enumeration cap may be arbitrarily larger or smaller than r. -/
theorem actual_small_product_le_four_pow {N cap r : ℕ} {w : ℝ}
    (hw : w ≤ (r : ℝ)) : actualSmallPrimeProduct N cap w ≤ 4 ^ r := by
  have hsub : actualSmallPrimeFinset N cap w ⊆ Nat.primesLE r := by
    intro p hp
    have h := mem_actualSmallPrimeFinset.mp hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, h.2.1⟩
    have hpR : (p : ℝ) ≤ r := h.2.2.2.le.trans hw
    exact_mod_cast hpR
  have hdiv := Finset.prod_dvd_prod_of_subset
    (actualSmallPrimeFinset N cap w) (Nat.primesLE r) id hsub
  have hdiv' : actualSmallPrimeProduct N cap w ∣ primorial r := by
    simpa only [actualSmallPrimeProduct, primorial_eq_prod_primesLE, id_eq] using hdiv
  exact (Nat.le_of_dvd (primorial_pos r) hdiv').trans (primorial_le_four_pow r)

/-- An explicit nonvacuous parameter range, uniform over ALL rough states
0<d<=D, every target, every enumeration cap, and both rough parities.
The input is only D*4^r*w^2<L, with w<=r; no Rosser gate is assumed. -/
theorem uniform_residual_small_signs_four_pow {N cap r e d : ℕ} {w L D : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hd : 0 < d)
    (hw : 1 ≤ w) (hwr : w ≤ (r : ℝ)) (hdD : (d : ℝ) ≤ D)
    (hbudget : D * ((4 : ℕ) ^ r : ℝ) * w ^ 2 < L) :
    actualSmallRosserPlus N cap w (L / (d : ℝ)) e = (-1 : ℝ) ^ e.primeFactors.card ∧
      actualSmallRosserMinus N cap w (L / (d : ℝ)) e = (-1 : ℝ) ^ e.primeFactors.card := by
  apply actual_residual_small_signs he hd hw
  have hM : (actualSmallPrimeProduct N cap w : ℝ) ≤ ((4 : ℕ) ^ r : ℝ) := by
    exact_mod_cast actual_small_product_le_four_pow (N := N) (cap := cap) hwr
  have hprod : (d : ℝ) * (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 ≤
      D * ((4 : ℕ) ^ r : ℝ) * w ^ 2 := by
    gcongr
  exact hprod.trans_lt hbudget

/-- Deleted target primes cannot remove more than the factor N: every
prime <=r lies in the actual product or divides N. This is exact arithmetic,
including primes on the wall r and arbitrary multiplicities in N. -/
theorem primorial_dvd_target_mul_actual {N cap r : ℕ} {w : ℝ}
    (hN : N ≠ 0) (hrw : (r : ℝ) < w) (hrcap : r < cap) :
    primorial r ∣ N * actualSmallPrimeProduct N cap w := by
  have hM0 := actualSmallPrimeProduct_ne_zero N cap w
  have hNM0 : N * actualSmallPrimeProduct N cap w ≠ 0 := mul_ne_zero hN hM0
  rw [← Nat.prod_primeFactors_of_squarefree (squarefree_primorial r),
    Nat.prod_primeFactors_dvd_iff hNM0, primeFactors_primorial]
  intro p hp
  have hpr := Nat.mem_primesLE.mp hp
  apply Nat.mem_primeFactors.mpr
  refine ⟨hpr.2, ?_, hNM0⟩
  by_cases hpN : p ∣ N
  · exact dvd_mul_of_dvd_left hpN _
  · have hpw : (p : ℝ) < w := (by exact_mod_cast hpr.1 : (p : ℝ) ≤ r).trans_lt hrw
    have hpM : p ∈ (actualSmallPrimeProduct N cap w).primeFactors := by
      rw [actualSmallPrimeProduct_primeFactors]
      exact mem_actualSmallPrimeFinset.mpr ⟨hpr.1.trans_lt hrcap, hpr.2, hpN, hpw⟩
    exact dvd_mul_of_dvd_right (Nat.mem_primeFactors.mp hpM).2.1 _

/-- Fully explicit lower obstruction to any automatic-product regime.
It can be applied to R=L/d and does not assume a prime number theorem. -/
theorem residual_lt_actual_of_primorial_obstruction {N cap r : ℕ} {w R : ℝ}
    (hN : N ≠ 0) (hrw : (r : ℝ) < w) (hrcap : r < cap)
    (hR : R * (N : ℝ) < (primorial r : ℝ)) :
    R < (actualSmallPrimeProduct N cap w : ℝ) := by
  have hdiv := primorial_dvd_target_mul_actual hN hrw hrcap
  have hle := Nat.le_of_dvd
    (Nat.mul_pos (Nat.pos_of_ne_zero hN)
      (Nat.pos_of_ne_zero (actualSmallPrimeProduct_ne_zero N cap w))) hdiv
  have hleR : (primorial r : ℝ) ≤ (N : ℝ) * (actualSmallPrimeProduct N cap w : ℝ) := by
    exact_mod_cast hle
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  nlinarith

/-- Under the lower obstruction even the full-carrier total cutoff fails.
Both actual coefficients vanish at the full small product. -/
theorem full_small_product_zero_of_primorial_obstruction {N cap r : ℕ} {w R : ℝ}
    (hN : N ≠ 0) (hrw : (r : ℝ) < w) (hrcap : r < cap)
    (hR : R * (N : ℝ) < (primorial r : ℝ)) :
    actualSmallRosserPlus N cap w R (actualSmallPrimeProduct N cap w) = 0 ∧
      actualSmallRosserMinus N cap w R (actualSmallPrimeProduct N cap w) = 0 := by
  have hcut := (residual_lt_actual_of_primorial_obstruction hN hrw hrcap hR).le
  exact ⟨MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_eq_zero_of_level_le hcut,
    MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_eq_zero_of_level_le hcut⟩

/-- The actual-product sufficient regime is excluded by this explicit
finite primorial obstruction. No asymptotic hypothesis is hidden here. -/
theorem not_product_regime_of_primorial_obstruction {N cap r : ℕ} {w R : ℝ}
    (hN : N ≠ 0) (hrw : (r : ℝ) < w) (hrcap : r < cap) (hw : 1 ≤ w)
    (hR : R * (N : ℝ) < (primorial r : ℝ)) :
    ¬ (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < R := by
  have hcut := residual_lt_actual_of_primorial_obstruction hN hrw hrcap hR
  have hM0 : (0 : ℝ) ≤ actualSmallPrimeProduct N cap w := Nat.cast_nonneg _
  have hw2 : (1 : ℝ) ≤ w ^ 2 := by nlinarith
  nlinarith
/-- The pinned elementary Chebyshev lower bound makes the obstruction
explicit in logarithms. All constants here belong to the proved bound. -/
theorem actual_small_log_lower {N cap r : ℕ} {w : ℝ}
    (hN : N ≠ 0) (hrw : (r : ℝ) < w) (hrcap : r < cap) :
    (r : ℝ) * Real.log 2 - Real.log ((r : ℝ) + 1) -
      2 * Real.sqrt (r : ℝ) * Real.log (r : ℝ) ≤
      Real.log (N : ℝ) + Real.log (actualSmallPrimeProduct N cap w : ℝ) := by
  have hdiv := primorial_dvd_target_mul_actual hN hrw hrcap
  have hle := Nat.le_of_dvd
    (Nat.mul_pos (Nat.pos_of_ne_zero hN)
      (Nat.pos_of_ne_zero (actualSmallPrimeProduct_ne_zero N cap w))) hdiv
  have hleR : (primorial r : ℝ) ≤ (N : ℝ) * (actualSmallPrimeProduct N cap w : ℝ) := by
    exact_mod_cast hle
  have hlog := Real.log_le_log
    (show (0 : ℝ) < primorial r by exact_mod_cast primorial_pos r) hleR
  rw [Real.log_mul (by exact_mod_cast hN)
    (by exact_mod_cast actualSmallPrimeProduct_ne_zero N cap w)] at hlog
  have htheta := Chebyshev.theta_ge r
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at htheta
  exact htheta.trans hlog

end
end ImbalancedChen.P5Z.PresieveGateRegime

