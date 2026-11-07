import ImbalancedChen.P5OriginalKFeedbackBudget
import ImbalancedChen.RenewalFiniteErrorPropagationP5

/-!
# Explicit original local precision for 441 finite generations

SOURCE ONLY; UNCOMPILED. Earlier delivered sources are frozen.

The original action-mass bound 12 and original root norm 7/2 are kept
literal. The local tolerance is a specific rational expression in the
original reserve and integer 12^441, not an existential precision choice.
Density and compiler errors have separate allocations of this tolerance.
No finite-table value or action-integral mass bound is certified here.
-/

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section

open P5RenewalFiniteError
open scoped BigOperators

def originalGenerationCount : ℕ := 441
def originalTransitionMass : ℝ := 12
def originalRootNorm : ℝ := 7 / 2
def originalGenerationPower : ℝ := originalTransitionMass ^ originalGenerationCount

/-- A completely explicit positive rational tolerance. The reserve is the
literal final B0, and the power is an integer expression. -/
def original441LocalAccuracy : ℝ :=
  22 *
    (2913305608548241964824517919947906098888971 /
      5485905019957289209587556738836463616000000000) /
    (7 * (12 : ℝ) ^ 441)

def originalDensityLocalAccuracy : ℝ := original441LocalAccuracy
def originalCompilerLocalAccuracy : ℝ := original441LocalAccuracy

private theorem one_le_twelve_pow (n : ℕ) : (1 : ℝ) ≤ 12 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    nlinarith only [ih]

theorem originalGenerationPower_ge_one : 1 ≤ originalGenerationPower := by
  exact one_le_twelve_pow 441

theorem originalGenerationPower_pos : 0 < originalGenerationPower := by
  linarith [originalGenerationPower_ge_one]

theorem originalReserve_pos : 0 < eachReserve := by
  rw [eachReserve_value]
  norm_num

theorem original441LocalAccuracy_eq :
    original441LocalAccuracy = 22 * eachReserve / (7 * originalGenerationPower) := by
  rw [eachReserve_value]
  rfl

theorem original441LocalAccuracy_pos : 0 < original441LocalAccuracy := by
  rw [original441LocalAccuracy_eq]
  exact div_pos (mul_pos (by norm_num) originalReserve_pos)
    (mul_pos (by norm_num) originalGenerationPower_pos)

theorem originalDensityLocalAccuracy_pos : 0 < originalDensityLocalAccuracy :=
  original441LocalAccuracy_pos

theorem originalCompilerLocalAccuracy_pos : 0 < originalCompilerLocalAccuracy :=
  original441LocalAccuracy_pos

/-- The original finite-generation geometric amplification, before root
normalization. Its mass12 semantic bound is a separate supplier. -/
def original441PropagationAllowance : ℝ :=
  original441LocalAccuracy * (originalGenerationPower - 1) / 11

/-- This is already in Chen coefficient units: 14/4 = 7/2. -/
def original441RootAllowance : ℝ := originalRootNorm * original441PropagationAllowance

theorem originalRootNorm_original_quarter : originalRootNorm = (14 : ℝ) / 4 := by
  norm_num [originalRootNorm]

theorem original441PropagationAllowance_nonneg : 0 ≤ original441PropagationAllowance := by
  exact div_nonneg
    (mul_nonneg original441LocalAccuracy_pos.le
      (sub_nonneg.mpr originalGenerationPower_ge_one)) (by norm_num)

theorem original441RootAllowance_exact :
    original441RootAllowance = eachReserve - eachReserve / originalGenerationPower := by
  rw [original441RootAllowance, original441PropagationAllowance,
    original441LocalAccuracy_eq]
  dsimp [originalRootNorm]
  field_simp [ne_of_gt originalGenerationPower_pos] <;> ring

theorem original441RootAllowance_lt_reserve : original441RootAllowance < eachReserve := by
  rw [original441RootAllowance_exact]
  have hpositive : 0 < eachReserve / originalGenerationPower :=
    div_pos originalReserve_pos originalGenerationPower_pos
  linarith

theorem original441RootAllowance_nonneg : 0 ≤ original441RootAllowance := by
  exact mul_nonneg (by norm_num [originalRootNorm]) original441PropagationAllowance_nonneg

/-- One entire original reserve is available for each of the two distinct
error species. Neither reserve is reused by the other species. -/
theorem original441_two_allocations_fit :
    original441RootAllowance + original441RootAllowance < 2 * eachReserve := by
  linarith [original441RootAllowance_lt_reserve]

/-- The owner's real recurrence is instantiated at the literal original
depth and at the explicit local accuracy, without an existential choice. -/
theorem original441_owner_amplification_exact :
    original441LocalAccuracy * amplification 441 = original441PropagationAllowance := by
  rw [amplification_eq_geometric]
  dsimp [original441PropagationAllowance, originalGenerationPower,
    originalTransitionMass, originalGenerationCount]
  ring

theorem original441_owner_root_reserve
    (X Y : Fin 11 → ℝ)
    (hentry : ∀ i, |X i - Y i| ≤ original441LocalAccuracy * amplification 441) :
    |rootValue X - rootValue Y| < eachReserve := by
  apply root_reserve_of_entry_errors X Y eachReserve original441LocalAccuracy
    original441LocalAccuracy_pos.le hentry
  have h := original441RootAllowance_lt_reserve
  change originalRootNorm * original441PropagationAllowance < eachReserve at h
  rw [← original441_owner_amplification_exact] at h
  simpa only [originalRootNorm, amplification_eq_geometric] using h

/-- Actual finite positive-action iteration on the original 400-cell state
space. The hypotheses retain every local atom, its mass bound12, and its
coefficient error bound. No original action integral is certified by an
unexplained action-result or final-table soundness field. The selected
queries state explicitly which entries enter this finite root evaluation. -/
theorem original441_positive_operator_root_error_lt_reserve
    {Act Atom : Type*}
    (atoms : ℕ → Act → Finset Atom)
    (child : ℕ → Act → Atom → OriginalState)
    (target : ℕ → Act → OriginalState) (bank : ℕ → List Act)
    (baseA baseB : ℕ → Act → ℝ) (weightA weightB : ℕ → Act → Atom → ℝ)
    (seed : OriginalState → ℝ) (query : Fin 11 → OriginalState)
    (hw : ∀ n a, a ∈ bank n → ∀ i ∈ atoms n a, 0 ≤ weightA n a i)
    (hmass : ∀ n a, a ∈ bank n → (∑ i ∈ atoms n a, weightA n a i) ≤ 12)
    (hlocal : ∀ n a, a ∈ bank n →
      localBudget (atoms n) (child n) (baseA n) (baseB n) (weightA n) (weightB n)
        (iterate atoms child target bank baseB weightB seed n) a ≤ original441LocalAccuracy) :
    |rootValue (fun i => iterate atoms child target bank baseA weightA seed 441 (query i)) -
      rootValue (fun i => iterate atoms child target bank baseB weightB seed 441 (query i))| <
      eachReserve := by
  have hiteration := iterate_error atoms child target bank baseA baseB weightA weightB seed
    original441LocalAccuracy original441LocalAccuracy_pos.le hw hmass hlocal 441
  exact original441_owner_root_reserve _ _ (fun i => hiteration (query i))

/-- The P4-A coefficient is fixed to the explicit positive accuracy 1e-8;
the two finite-generation allocations are paid in addition, from the two
original B0 reserves. This is only the scalar coefficient conclusion. -/
theorem original441_and_density_delta_keep_currentC :
    currentC < adoptedRawWithDensityCoefficient (currentK + allowedDensityDelta) -
      original441RootAllowance - original441RootAllowance := by
  have hfixed := (currentC_of_density_coefficient_delta
    allowedDensityDelta_pos.le (le_refl allowedDensityDelta)).2.2
  have halloc := original441_two_allocations_fit
  linarith

/-- A consumer may pass the separately established root-scale density and
compiler errors. It must first obtain their bounds from the actual finite
operators. No whole lower mean is hypothesized. -/
theorem original441_separate_root_errors_keep_currentC (densityError compilerError : ℝ)
    (hdensity : densityError ≤ originalRootNorm *
      (originalDensityLocalAccuracy * (originalGenerationPower - 1) / 11))
    (hcompiler : compilerError ≤ originalRootNorm *
      (originalCompilerLocalAccuracy * (originalGenerationPower - 1) / 11)) :
    currentC < adoptedRawWithDensityCoefficient (currentK + allowedDensityDelta) -
      densityError - compilerError := by
  change densityError ≤ original441RootAllowance at hdensity
  change compilerError ≤ original441RootAllowance at hcompiler
  linarith [original441_and_density_delta_keep_currentC]

/-- Two separate root-input approximation certificates can now be paid by
the two original reserves, after the fixed P4-A density error. The input
errors may each be produced by the positive-operator theorem above, or by
the original integral-to-root comparison with its own actual local proof. -/
theorem original441_two_root_certificates_keep_currentC
    (densityA densityB compilerA compilerB : Fin 11 → ℝ)
    (hdensity : ∀ i, |densityA i - densityB i| ≤
      originalDensityLocalAccuracy * amplification 441)
    (hcompiler : ∀ i, |compilerA i - compilerB i| ≤
      originalCompilerLocalAccuracy * amplification 441) :
    currentC < adoptedRawWithDensityCoefficient (currentK + allowedDensityDelta) -
      |rootValue densityA - rootValue densityB| -
      |rootValue compilerA - rootValue compilerB| := by
  have hd := original441_owner_root_reserve densityA densityB hdensity
  have hc := original441_owner_root_reserve compilerA compilerB hcompiler
  have hfixed := (currentC_of_density_coefficient_delta
    allowedDensityDelta_pos.le (le_refl allowedDensityDelta)).2.2
  linarith

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
