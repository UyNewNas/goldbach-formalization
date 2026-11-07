import ImbalancedChen.SingularSeries
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# Logarithmic savings pay fixed and logarithmically many atoms

SOURCE ONLY / YELLOW / UNCOMPILED (2026-10-24).

The linear numerator `N` is permitted here: the saving comes from at least
one extra power of `log N` beyond the normalization's squared logarithm.
This does not apply the sublinear-power budget with exponent one.

All coefficients, atom counts and natural logarithm exponents are fixed
before the tolerance and the common natural threshold are chosen. The only
limit used is the proved divergence of `log N`; the comparison with the
actual normalization uses its proved positive singular-series lower bound.
No PNT, density, distribution or other analytic estimate is a premise.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- A fixed logarithm power in the atom count is paid whenever the
denominator retains at least three logarithm powers after cancellation.
The coefficient is allowed to vanish. -/
theorem eventually_logPower_atoms_le_singularNormalization
    (C : ℝ) (_hC : 0 ≤ C) (k A : ℕ) (hA : k + 3 ≤ A)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧
        C * (N : ℝ) * (Real.log (N : ℝ)) ^ k /
          (Real.log (N : ℝ)) ^ A ≤ eta * singularNormalization N := by
  have hlogLimit : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowerLimit :
      Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ (A - (k + 2)))
        atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (n := A - (k + 2)) (by omega)).comp hlogLimit
  have hratio : Tendsto
      (fun N : ℕ => C / (Real.log (N : ℝ)) ^ (A - (k + 2)))
      atTop (𝓝 0) := hpowerLimit.const_div_atTop C
  have hsmall : ∀ᶠ N : ℕ in atTop,
      C / (Real.log (N : ℝ)) ^ (A - (k + 2)) < eta * twinPrimeConstant :=
    hratio.eventually (gt_mem_nhds (mul_pos heta twinPrimeConstant_pos))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNreal)
  have hbase : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  have hsplit : A - (k + 2) + (k + 2) = A := by omega
  have hpower : (Real.log (N : ℝ)) ^ A =
      (Real.log (N : ℝ)) ^ (A - (k + 2)) *
        ((Real.log (N : ℝ)) ^ k * (Real.log (N : ℝ)) ^ 2) := by
    symm
    simpa only [pow_add] using
      congrArg (fun j : ℕ => (Real.log (N : ℝ)) ^ j) hsplit
  refine ⟨hN, ?_⟩
  calc
    C * (N : ℝ) * (Real.log (N : ℝ)) ^ k /
        (Real.log (N : ℝ)) ^ A =
        (C / (Real.log (N : ℝ)) ^ (A - (k + 2))) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      rw [hpower]
      field_simp [hlog] <;> ring
    _ ≤ (eta * twinPrimeConstant) *
        ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hsmallN.le hbase
    _ = eta * (twinPrimeConstant * (N : ℝ) /
        (Real.log (N : ℝ)) ^ 2) := by ring
    _ ≤ eta * singularNormalization N :=
      mul_le_mul_of_nonneg_left (singularNormalization_lower N) heta.le

/-- Any fixed `C >= 0` and natural `A >= 3` give an arbitrarily small
normalized error `C N / (log N)^A`, on the same eventual set as `N >= 2`. -/
theorem eventually_logSaving_le_singularNormalization
    (C : ℝ) (hC : 0 ≤ C) (A : ℕ) (hA : 3 ≤ A)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ C * (N : ℝ) / (Real.log (N : ℝ)) ^ A ≤
        eta * singularNormalization N := by
  simpa only [Nat.zero_add, pow_zero, mul_one] using
    eventually_logPower_atoms_le_singularNormalization C hC 0 A hA eta heta

/-- A fixed finite number of atoms changes only the fixed coefficient.
The returned eventual set is common to their aggregate cost and `N >= 2`. -/
theorem eventually_fixed_atoms_logSaving_le_singularNormalization
    (M : ℕ) (C : ℝ) (hC : 0 ≤ C) (A : ℕ) (hA : 3 ≤ A)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧
        (M : ℝ) * (C * (N : ℝ) / (Real.log (N : ℝ)) ^ A) ≤
          eta * singularNormalization N := by
  filter_upwards
    [eventually_logSaving_le_singularNormalization ((M : ℝ) * C)
      (mul_nonneg (Nat.cast_nonneg M) hC) A hA eta heta] with N hN
  refine ⟨hN.1, ?_⟩
  calc
    (M : ℝ) * (C * (N : ℝ) / (Real.log (N : ℝ)) ^ A) =
        ((M : ℝ) * C) * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring
    _ ≤ eta * singularNormalization N := hN.2

/-- Complete log-power atom supplier, with one explicit threshold `N0 >= 2`.
The threshold may depend on the fixed inputs and the requested tolerance. -/
theorem exists_logPower_atoms_normalization_threshold
    (C : ℝ) (hC : 0 ≤ C) (k A : ℕ) (hA : k + 3 ≤ A) :
    ∀ eta : ℝ, 0 < eta →
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
        C * (N : ℝ) * (Real.log (N : ℝ)) ^ k /
          (Real.log (N : ℝ)) ^ A ≤ eta * singularNormalization N := by
  intro eta heta
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_logPower_atoms_le_singularNormalization C hC k A hA eta heta)
  refine ⟨max M 2, le_max_right _ _, ?_⟩
  intro N hN
  exact (hM N (le_trans (le_max_left _ _) hN)).2

/-- The basic linear-numerator log-saving supplier has no analytic premise. -/
theorem exists_logSaving_normalization_threshold
    (C : ℝ) (hC : 0 ≤ C) (A : ℕ) (hA : 3 ≤ A) :
    ∀ eta : ℝ, 0 < eta →
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A ≤
          eta * singularNormalization N := by
  intro eta heta
  simpa only [Nat.zero_add, pow_zero, mul_one] using
    exists_logPower_atoms_normalization_threshold C hC 0 A hA eta heta

/-- A complete supplier for the sum of a fixed finite number of atom costs.
In particular `M = 0` and `C = 0` need no separate analytic argument. -/
theorem exists_fixed_atoms_logSaving_normalization_threshold
    (M : ℕ) (C : ℝ) (hC : 0 ≤ C) (A : ℕ) (hA : 3 ≤ A) :
    ∀ eta : ℝ, 0 < eta →
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
        (M : ℝ) * (C * (N : ℝ) / (Real.log (N : ℝ)) ^ A) ≤
          eta * singularNormalization N := by
  intro eta heta
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    (eventually_fixed_atoms_logSaving_le_singularNormalization M C hC A hA eta heta)
  refine ⟨max L 2, le_max_right _ _, ?_⟩
  intro N hN
  exact (hL N (le_trans (le_max_left _ _) hN)).2

end

end ImbalancedChen
