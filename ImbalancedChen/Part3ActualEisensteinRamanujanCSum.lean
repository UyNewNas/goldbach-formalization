import ImbalancedChen.Part3ActualEisensteinPositiveCFourier
import ImbalancedChen.P0RamanujanMultiplicativeGcdBound
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual parabolic Eisenstein coefficient is evaluated as the genuine
level-restricted Ramanujan Dirichlet series times the proved power-seed
Fourier transform. This is an infinite positive-c result, after the actual
primitive-row grouping and integral interchange. The arithmetic series is
itself absolutely convergent for s>1, from the actual Ramanujan gcd bound
and a native p-series comparison. At n=0 the literal phi(c) Dirichlet
factor multiplies the Gamma quotient; at n!=0 the actual real-order K
factor multiplies the literal Ramanujan c sum. N|c is explicit, including
level zero. The further divisor/zeta evaluation is deliberately OPEN.
-/

namespace ImbalancedChen.Part3.ActualEisensteinRamanujanCSum20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini
open ImbalancedChen.Part3.PowerSeedPeriodization
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.ActualEisensteinFixedCFourier20261025a
open ImbalancedChen.Part3.ActualEisensteinPositiveCFourier20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.RamanujanMultiplicativeGcdBound20261025a

/-- The actual arithmetic coefficient at positive c, with its literal
level condition. This is not a free supplier for a Fourier coefficient. -/
def levelRamanujanTerm (N : ℕ) (s : ℝ) (n : ℤ) (c : ℕ+) : ℂ :=
  if N ∣ (c : ℕ) then ((c : ℝ) ^ (-(2 * s)) : ℂ) * ramanujan (c : ℕ) n else 0

/-- The true positive-c, level-restricted Ramanujan Dirichlet series. -/
def levelRamanujanSeries (N : ℕ) (s : ℝ) (n : ℤ) : ℂ :=
  ∑' c : ℕ+, levelRamanujanTerm N s n c

/-- The n=0 arithmetic term is Euler's actual totient. -/
def levelTotientTerm (N : ℕ) (s : ℝ) (c : ℕ+) : ℝ :=
  if N ∣ (c : ℕ) then (c : ℝ) ^ (-(2 * s)) * ((c : ℕ).totient : ℝ) else 0

/-- Quantitative convergence bound for the actual arithmetic coefficient. -/
theorem levelRamanujanTerm_norm_le (N : ℕ) (s : ℝ) (n : ℤ) (c : ℕ+) :
    ‖levelRamanujanTerm N s n c‖ ≤ (c : ℝ) ^ (1 - 2 * s) := by
  have hc : 0 < (c : ℝ) := by exact_mod_cast c.property
  have hg : ‖ramanujan (c : ℕ) n‖ ≤ (c : ℝ) := by
    apply (norm_ramanujan_le_gcd (c : ℕ) n).trans
    exact_mod_cast (Nat.le_of_dvd c.property (Nat.gcd_dvd_left (c : ℕ) n.natAbs))
  by_cases hNc : N ∣ (c : ℕ)
  · rw [levelRamanujanTerm, if_pos hNc, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hc.le _)]
    calc
      _ ≤ (c : ℝ) ^ (-(2 * s)) * (c : ℝ) :=
        mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hc.le _)
      _ = (c : ℝ) ^ (1 - 2 * s) := by
        rw [show 1 - 2 * s = -(2 * s) + 1 by ring, Real.rpow_add hc, Real.rpow_one]
  · simp only [levelRamanujanTerm, if_neg hNc, norm_zero]
    exact Real.rpow_nonneg hc.le _

/-- ABSOLUTE convergence of the actual Ramanujan c sum. No Fourier
interchange, summability field, or hAbsSum is assumed here. -/
theorem levelRamanujanTerm_norm_summable (N : ℕ) (s : ℝ) (hs : 1 < s) (n : ℤ) :
    Summable (fun c : ℕ+ => ‖levelRamanujanTerm N s n c‖) := by
  have h : Summable (fun c : ℕ => (c : ℝ) ^ (1 - 2 * s)) :=
    summable_nat_rpow.mpr (by linarith)
  exact (h.subtype (fun c : ℕ => 0 < c)).of_nonneg_of_le
    (fun c => norm_nonneg _) (levelRamanujanTerm_norm_le N s n)

theorem levelRamanujanTerm_summable (N : ℕ) (s : ℝ) (hs : 1 < s) (n : ℤ) :
    Summable (levelRamanujanTerm N s n) :=
  (levelRamanujanTerm_norm_summable N s hs n).of_norm

theorem levelRamanujanTerm_zero (N : ℕ) (s : ℝ) (c : ℕ+) :
    levelRamanujanTerm N s 0 c = (levelTotientTerm N s c : ℂ) := by
  letI : NeZero (c : ℕ) := ⟨Nat.ne_of_gt c.property⟩
  by_cases hNc : N ∣ (c : ℕ) <;>
    simp [levelRamanujanTerm, levelTotientTerm, hNc, ramanujan_at_zero]

theorem levelTotientTerm_nonneg (N : ℕ) (s : ℝ) (c : ℕ+) :
    0 ≤ levelTotientTerm N s c := by
  unfold levelTotientTerm
  split_ifs <;> positivity

/-- The literal Euler-phi Dirichlet factor is genuinely summable. -/
theorem levelTotientTerm_summable (N : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (levelTotientTerm N s) := by
  have h := levelRamanujanTerm_norm_summable N s hs 0
  simpa only [levelRamanujanTerm_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (levelTotientTerm_nonneg N s _)] using h

/-- At a forbidden c the ACTUAL primitive level row fiber is empty. -/
theorem fixedFirstFourier_eq_zero_of_not_level (N c : ℕ)
    (hNc : ¬ N ∣ c) (s y : ℝ) (hy : 0 < y) (n : ℤ) :
    fixedFirstFourier N c s y hy n = 0 := by
  letI : IsEmpty (PrimitiveD N (c : ℤ)) :=
    ⟨fun d => hNc (Int.natCast_dvd_natCast.mp d.property.2)⟩
  simp [fixedFirstFourier, fixedFirstBlock]

/-- The full primitive-block coefficient equals the actual arithmetic
term at every positive c, including those prohibited by the level. -/
theorem fixedFirstFourier_eq_levelRamanujan (N : ℕ) (c : ℕ+)
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    fixedFirstFourier N (c : ℕ) s y hy n = levelRamanujanTerm N s n c *
      ∫ x in (0 : ℝ)..1, fourierPhase n x * (periodizedPowerSeed s y x : ℂ) := by
  letI : NeZero (c : ℕ) := ⟨Nat.ne_of_gt c.property⟩
  by_cases hNc : N ∣ (c : ℕ)
  · rw [fixedFirstFourier_eq_ramanujan N (c : ℕ)
      (Int.natCast_dvd_natCast.mpr hNc) s hs y hy n]
    simp only [levelRamanujanTerm, if_pos hNc]
  · rw [fixedFirstFourier_eq_zero_of_not_level N (c : ℕ) hNc]
    simp only [levelRamanujanTerm, if_neg hNc, zero_mul]

/-- The FULL actual GammaInfinity\Gamma0 Eisenstein coefficient, with
its actual height contribution and absolutely convergent arithmetic c sum. -/
theorem actualEisensteinFourier_eq_ramanujan_series (N : ℕ)
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    actualEisensteinFourier N s y hy n = heightFourier s y n +
      levelRamanujanSeries N s n *
        ∫ x in (0 : ℝ)..1, fourierPhase n x * (periodizedPowerSeed s y x : ℂ) := by
  rw [actualEisensteinFourier_eq_positive_c_sum N s hs y hy n]
  simp_rw [fixedFirstFourier_eq_levelRamanujan N _ s hs y hy n]
  simp only [levelRamanujanSeries, tsum_mul_right]

/-- Actual ZERO coefficient: y^s plus the exact Gamma quotient times
its genuine level-restricted phi(c) Dirichlet factor. -/
theorem actualEisensteinFourier_zero (N : ℕ)
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) :
    actualEisensteinFourier N s y hy 0 =
      ((y ^ s +
        (Real.sqrt Real.pi * Real.Gamma (s - 1 / 2) / Real.Gamma s) * y ^ (1 - s) *
          ∑' c : ℕ+, levelTotientTerm N s c : ℝ) : ℂ) := by
  have hs' : (1 / 2 : ℝ) < s := by linarith
  have harith : levelRamanujanSeries N s 0 =
      ((∑' c : ℕ+, levelTotientTerm N s c : ℝ) : ℂ) := by
    simp only [levelRamanujanSeries, levelRamanujanTerm_zero, Complex.ofReal_tsum]
  rw [actualEisensteinFourier_eq_ramanujan_series N s hs y hy 0, harith,
    periodizedPowerSeed_fourier_unfold hs' hy]
  simp only [fourierPhase, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [integral_ofReal, ImbalancedChen.Part3RealPowerSeedConstantMode.integral_powerSeed hs' hy]
  simp only [heightFourier, if_true]
  push_cast
  ring

/-- Actual NONZERO coefficient: the literal convergent Ramanujan c sum
with N|c times the canonical Gamma/real-order-K height and frequency factor. -/
theorem actualEisensteinFourier_nonzero (N : ℕ)
    (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) :
    actualEisensteinFourier N s y hy n = levelRamanujanSeries N s n *
      (((2 * Real.pi ^ s / Real.Gamma s * |(n : ℝ)| ^ (s - 1 / 2) * Real.sqrt y *
        RealOrderKExceptionalSourceOnly.realOrderK (s - 1 / 2)
          (2 * Real.pi * |(n : ℝ)| * y) : ℝ) : ℂ)) := by
  rw [actualEisensteinFourier_eq_ramanujan_series N s hs y hy n,
    periodizedPowerSeed_nonzero_fourier_actualK (by linarith : (1 / 2 : ℝ) < s) hy hn]
  simp only [heightFourier, if_neg hn, zero_add]

end
end ImbalancedChen.Part3.ActualEisensteinRamanujanCSum20261025a

