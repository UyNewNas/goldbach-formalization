import ImbalancedChen.P5ZU1011OriginalSixteenPolicyBank
import ImbalancedChen.P5ZU1011H248CommonPartition

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Exact integral and actual-prime Fubini accounting for the ORIGINAL sixteen
policy bank, before any harmonic limit is taken. The nonlinear minimum is
frozen only AFTER all sixteen H248 states are simultaneously selected.
Each summand retains all original eligibility tests and the switched fallback.
No minimum of separately averaged policies is introduced.

The existing actual bank supplies the envelope integrability and ordinary
bounds. This module supplies the measurable common H248 pullbacks, the
weighted harmonic-density restriction, and the exact integral reassembly.
A tuple-dependent or moving mask is permitted only in finite identities;
no masked convergence theorem is asserted.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenReassembly

noncomputable section
open Set MeasureTheory Filter
open Classical
open U11Integral U11H248 U11Canonical U1011H248Partition U1011AdaptivePrimeError
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

abbrev BankState := CommonState U1011OriginalSixteenPolicyBank.bank

def switched : LogFour → ℝ := switchedKernel currentK LiLiuPrereqBuchstab.buchstab

def actualMinimum : LogFour → ℝ :=
  envelope U1011OriginalSixteenPolicyBank.bank
    (guarded U1011OriginalSixteenPolicyBank.eligible switched
      (ordinaryKernel H248 U1011OriginalSixteenPolicyBank.residual))

def cell (sigma : BankState) : Set LogFour :=
  commonCell U1011OriginalSixteenPolicyBank.bank
    U1011OriginalSixteenPolicyBank.residual sigma

def stateMinimum (sigma : BankState) : LogFour → ℝ :=
  envelope U1011OriginalSixteenPolicyBank.bank
    (guarded U1011OriginalSixteenPolicyBank.eligible switched
      (stateOrdinary U1011OriginalSixteenPolicyBank.bank
        U1011OriginalSixteenPolicyBank.residual sigma))

theorem measurableSet_scalarCell (a : AtomState) : MeasurableSet (scalarCell a) := by
  cases a with
  | none =>
      have heq : scalarCell none = Ioi (5 : ℝ) := by
        ext s
        exact mem_scalarCell_none_iff s
      rw [heq]
      exact measurableSet_Ioi
  | some b =>
      exact (measurableSet_upperAtomSet b).preimage (measurable_const.max measurable_id)

/-- All sixteen true residuals are read together, including every zero
exterior and marked knot. Division remains the actual total real division. -/
theorem measurableSet_cell (sigma : BankState) : MeasurableSet (cell sigma) := by
  simp only [cell, commonCell, setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_scalarCell (sigma j)).preimage
    ((U1011OriginalSixteenPolicyBank.measurable_residual j.val).div (measurable_pi_apply 3))

theorem stateMinimum_eq_actual {sigma : BankState} {v : LogFour}
    (hv : v ∈ cell sigma) : stateMinimum sigma v = actualMinimum v := by
  exact (envelope_eq_state hv U1011OriginalSixteenPolicyBank.eligible switched).symm

theorem measurable_actualMinimum : Measurable actualMinimum := by
  apply measurable_envelope
  apply measurable_guarded
  · intro j _
    exact U1011OriginalSixteenPolicyBank.measurableSet_eligible j
  · exact measurable_switchedKernel currentK _ LiLiuPrereqBuchstab.continuous_buchstab.measurable
  · intro j _
    exact measurable_ordinaryKernel H248 U1011OriginalSixteenPolicyBank.residual j
      measurable_H248 (U1011OriginalSixteenPolicyBank.measurable_residual j)

/-- This is a specialization of the existing actual bank bounds, with
all sixteen source masks and W retained in the SAME envelope. -/
theorem actualMinimum_bounds (mask : Set (ℝ×ℝ)) (v : LogFour)
    (hv : v ∈ originalDomain mask) : 0 ≤ actualMinimum v ∧ actualMinimum v ≤ switched v := by
  apply guarded_envelope_bounds (originalDomain mask)
    U1011OriginalSixteenPolicyBank.bank U1011OriginalSixteenPolicyBank.eligible
    switched (ordinaryKernel H248 U1011OriginalSixteenPolicyBank.residual)
  · exact canonical_switched_nonneg mask currentK (by norm_num [currentK])
  · intro j _ v hv he
    exact (U1011OriginalSixteenPolicyBank.ordinary_actual_bounds mask j v hv he).1
  · exact hv

theorem harmonicDensity_nonneg_on_original (mask : Set (ℝ×ℝ)) (v : LogFour)
    (hv : v ∈ originalDomain mask) : 0 ≤ harmonicDensity v := by
  have h := originalDomain_subset_compactBox mask hv
  have hp : ∀ i : Fin 4, 0 < v i := by
    intro i
    have hi : (417/5000 : ℝ) ≤ v i := h.1 i
    linarith
  exact div_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (mul_nonneg (hp 0).le (hp 1).le) (hp 2).le) (hp 3).le)

/-- The actual harmonic weight is inserted using the already proved
weighted switched majorant. No weighted mean or integrability premise is used. -/
theorem integrableOn_weighted_actualMinimum (mask : Set (ℝ×ℝ))
    (hm : MeasurableSet mask) :
    IntegrableOn (fun v => actualMinimum v * harmonicDensity v) (originalDomain mask) volume := by
  have hmeas : Measurable (fun v => actualMinimum v * harmonicDensity v) := by
    apply measurable_actualMinimum.mul
    unfold harmonicDensity
    fun_prop
  apply (integrableOn_original_weighted_switched mask currentK).mono_nonneg
    hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain mask hm)] with v hv
    exact mul_nonneg (actualMinimum_bounds mask v hv).1
      (harmonicDensity_nonneg_on_original mask v hv)
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain mask hm)] with v hv
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (actualMinimum_bounds mask v hv).2 (harmonicDensity_nonneg_on_original mask v hv)

/-- Every common state is integrable because its TRUE frozen minimum is
identical there to the actual original-bank minimum. -/
theorem integrableOn_stateIndicator (mask : Set (ℝ×ℝ)) (hm : MeasurableSet mask)
    (sigma : BankState) :
    IntegrableOn ((cell sigma).indicator
      (fun v => stateMinimum sigma v * harmonicDensity v)) (originalDomain mask) volume := by
  have heq : (cell sigma).indicator (fun v => stateMinimum sigma v * harmonicDensity v) =
      (cell sigma).indicator (fun v => actualMinimum v * harmonicDensity v) := by
    funext v
    by_cases hv : v ∈ cell sigma
    · simp only [indicator_of_mem hv, stateMinimum_eq_actual hv]
    · simp only [indicator_of_notMem hv]
  rw [heq]
  exact (integrableOn_weighted_actualMinimum mask hm).indicator (measurableSet_cell sigma)

/-- Exact nonlinear full-bank harmonic integral reassembly. The state sum
is outside the integral, while the policy minimum stays INSIDE each state. -/
theorem integral_actualMinimum_eq_common_state_sum (mask : Set (ℝ×ℝ))
    (hm : MeasurableSet mask) :
    (∫ v in originalDomain mask, actualMinimum v * harmonicDensity v) =
      ∑ sigma : BankState, ∫ v in originalDomain mask ∩ cell sigma,
        stateMinimum sigma v * harmonicDensity v := by
  calc
    _ = ∫ v in originalDomain mask, ∑ sigma : BankState,
        (cell sigma).indicator (fun v => stateMinimum sigma v * harmonicDensity v) v := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v =>
        weighted_minimum_eq_sum_states U1011OriginalSixteenPolicyBank.bank
          U1011OriginalSixteenPolicyBank.residual U1011OriginalSixteenPolicyBank.eligible
          switched harmonicDensity v)
    _ = ∑ sigma : BankState, ∫ v in originalDomain mask,
        (cell sigma).indicator (fun v => stateMinimum sigma v * harmonicDensity v) v := by
      apply integral_finsetSum
      intro sigma _
      exact integrableOn_stateIndicator mask hm sigma
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sigma _
      exact setIntegral_indicator (measurableSet_cell sigma)

/-- Literal finite harmonic Fubini on the actual prime tuples. Any keep
mask stays inside every common state. This is an equality at EACH N. -/
theorem actual_masked_harmonic_eq_common_state_sum (N : ℕ) (a b : Fin 4 → ℝ)
    (keep : (Fin 4 → ℕ) → Prop) :
    maskedTestSum N a b keep actualMinimum =
      ∑ sigma : BankState, maskedTestSum N a b
        (fun p => keep p ∧ actualPrimeTupleLog N p ∈ cell sigma) (stateMinimum sigma) := by
  exact actual_masked_minimum_eq_sum_states N a b keep
    U1011OriginalSixteenPolicyBank.bank U1011OriginalSixteenPolicyBank.residual
    U1011OriginalSixteenPolicyBank.eligible switched

end
end ImbalancedChen.P5Z.U1011OriginalSixteenReassembly


