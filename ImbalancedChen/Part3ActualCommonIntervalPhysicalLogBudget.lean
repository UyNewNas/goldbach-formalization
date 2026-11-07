import ImbalancedChen.Part3ActualCommonIntervalCompletionNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24. New source fragment.
Append after the actual norm-completion bundle. This fragment uses the real
PacketData.m_normalized field to license the period budget. Empty carriers
are dealt with by exact zero identities and do not require a bound on hi.
-/

namespace ImbalancedChen.Part3.ActualCommonIntervalPhysicalLogBudgetSourceOnly
noncomputable section

open Classical
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionL1SourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionNormSourceOnly

variable {ι : Type*}

def physicalPeriod (P : PacketData ι) : ℕ := max 2 (P.hi + 1)

theorem physicalPeriod_two_le (P : PacketData ι) : 2 ≤ physicalPeriod P := by
  exact le_max_left _ _

theorem hi_lt_physicalPeriod (P : PacketData ι) : P.hi < physicalPeriod P := by
  exact lt_of_lt_of_le (Nat.lt_succ_self P.hi) (le_max_right _ _)

instance physicalPeriod_neZero (P : PacketData ι) : NeZero (physicalPeriod P) :=
  ⟨by have h := physicalPeriod_two_le P; omega⟩

/-- The actual upper normalized-coordinate gate controls the LAST natural m. -/
theorem hi_le_of_mCarrier_nonempty (P : PacketData ι) (hne : P.mCarrier.Nonempty) :
    (P.hi : ℝ) ≤ 32 * P.V + 1 := by
  rcases hne with ⟨m, hm⟩
  have hmem := Finset.mem_Ico.mp hm
  have hlohi : P.lo < P.hi := by omega
  have hlast : P.hi - 1 ∈ P.mCarrier := by
    apply Finset.mem_Ico.mpr
    omega
  have hupper := (P.m_normalized (P.hi - 1) hlast).2
  have hlastBound : ((P.hi - 1 : ℕ) : ℝ) < 32 * P.V :=
    (div_lt_iff₀ P.V_pos).mp hupper
  have hnat : P.hi - 1 + 1 = P.hi := by omega
  have hcast : ((P.hi - 1 : ℕ) : ℝ) + 1 = (P.hi : ℝ) := by
    exact_mod_cast hnat
  linarith

theorem physicalPeriod_le_linear (P : PacketData ι) (hne : P.mCarrier.Nonempty) :
    (physicalPeriod P : ℝ) ≤ 32 * P.V + 3 := by
  have hhi := hi_le_of_mCarrier_nonempty P hne
  simp only [physicalPeriod, Nat.cast_max, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  apply max_le
  · linarith [P.V_pos]
  · linarith

/-- A fixed sixth power absorbs the physical linear period budget. -/
theorem physicalPeriod_le_sixth_power (P : PacketData ι) (hne : P.mCarrier.Nonempty) :
    (physicalPeriod P : ℝ) ≤ (2 + P.V)^6 := by
  have hbase : (2 : ℝ) ≤ 2 + P.V := by linarith [P.V_pos]
  have hpow : (32 : ℝ) ≤ (2 + P.V)^5 := by
    calc
      (32 : ℝ) = (2 : ℝ)^5 := by norm_num
      _ ≤ (2 + P.V)^5 := pow_le_pow_left₀ (by norm_num) hbase 5
  calc
    (physicalPeriod P : ℝ) ≤ 32 * (2 + P.V) := by
      linarith [physicalPeriod_le_linear P hne]
    _ ≤ (2 + P.V)^5 * (2 + P.V) :=
      mul_le_mul_of_nonneg_right hpow (by linarith [P.V_pos])
    _ = (2 + P.V)^6 := by ring

/-- A single absolute mask-completion constant, independent of all packet data. -/
def physicalCompletionConstant : ℝ := 6 + 2 / Real.log 2

theorem physicalCompletionConstant_pos : 0 < physicalCompletionConstant := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold physicalCompletionConstant
  positivity

theorem physicalPeriod_log_bound (P : PacketData ι) (hne : P.mCarrier.Nonempty) :
    2 + Real.log (physicalPeriod P : ℝ) ≤
      physicalCompletionConstant * Real.log (2 + P.V) := by
  have hperiodPos : (0 : ℝ) < (physicalPeriod P : ℝ) := by
    exact_mod_cast (show 0 < physicalPeriod P by have h := physicalPeriod_two_le P; omega)
  have hlogPeriod : Real.log (physicalPeriod P : ℝ) ≤ 6 * Real.log (2 + P.V) := by
    calc
      Real.log (physicalPeriod P : ℝ) ≤ Real.log ((2 + P.V)^6) :=
        Real.log_le_log hperiodPos (physicalPeriod_le_sixth_power P hne)
      _ = 6 * Real.log (2 + P.V) := by rw [Real.log_pow]; norm_num
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogBase : Real.log (2 : ℝ) ≤ Real.log (2 + P.V) :=
    Real.log_le_log (by norm_num) (by linarith [P.V_pos])
  have hconstant : 2 ≤ (2 / Real.log (2 : ℝ)) * Real.log (2 + P.V) := by
    calc
      (2 : ℝ) = (2 / Real.log (2 : ℝ)) * Real.log (2 : ℝ) := by
        field_simp [hlogTwo.ne']
      _ ≤ (2 / Real.log (2 : ℝ)) * Real.log (2 + P.V) :=
        mul_le_mul_of_nonneg_left hlogBase (by positivity)
  unfold physicalCompletionConstant
  nlinarith

theorem actual_completion_l1_physical_nonempty (P : PacketData ι)
    (a b : ℕ) (hne : P.mCarrier.Nonempty) :
    (∑ r : ZMod (physicalPeriod P),
      ‖normalizedFourierCoeff P a b (physicalPeriod P) r‖) ≤
        physicalCompletionConstant * Real.log (2 + P.V) := by
  exact (actual_common_interval_completion_l1 P a b (physicalPeriod P)
    (physicalPeriod_two_le P) (hi_lt_physicalPeriod P)).trans (physicalPeriod_log_bound P hne)

theorem completedPacketSum_zero_of_mCarrier_empty (P : PacketData ι)
    (hempty : P.mCarrier = ∅) (k : D4 → ℤ) : completedPacketSum P k = 0 := by
  simp only [completedPacketSum, hempty, Finset.sum_empty, Finset.sum_const_zero]

theorem restrictedPacketSum_zero_of_mCarrier_empty (P : PacketData ι)
    (hempty : P.mCarrier = ∅) (a b : ℕ) (k : D4 → ℤ) :
    completedPacketSum (restrictM P a b) k = 0 := by
  apply completedPacketSum_zero_of_mCarrier_empty
  rw [restrictM_mCarrier, hempty, Finset.inter_empty]

theorem shiftedPacketSum_zero_of_mCarrier_empty (P : PacketData ι)
    (hempty : P.mCarrier = ∅) (k : D4 → ℤ) (N : ℕ) [NeZero N] (r : ZMod N) :
    shiftedPacketSum P k N r = 0 := by
  simp only [shiftedPacketSum, hempty, Finset.sum_empty, Finset.sum_const_zero]

theorem maxShiftedPacketNorm_zero_of_mCarrier_empty (P : PacketData ι)
    (hempty : P.mCarrier = ∅) (k : D4 → ℤ) (N : ℕ) [NeZero N] :
    maxShiftedPacketNorm P k N = 0 := by
  unfold maxShiftedPacketNorm
  apply Finset.sup'_eq_of_forall
  intro r _hr
  rw [shiftedPacketSum_zero_of_mCarrier_empty P hempty k N r, norm_zero]

/-- Unconditional physical-log mask cost. The empty branch is exactly zero;
its potentially arbitrary hi never enters the geometric period estimate. -/
theorem actual_same_mask_physical_norm (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) :
    ‖completedPacketSum (restrictM P a b) k‖ ≤
      (physicalCompletionConstant * Real.log (2 + P.V)) *
        maxShiftedPacketNorm P k (physicalPeriod P) := by
  by_cases hne : P.mCarrier.Nonempty
  · exact (actual_restrictedPacket_norm_le_completion_max P a b (physicalPeriod P)
      (physicalPeriod_two_le P) (hi_lt_physicalPeriod P) k).trans
      (mul_le_mul_of_nonneg_right (physicalPeriod_log_bound P hne)
        (maxShiftedPacketNorm_nonneg P k (physicalPeriod P)))
  · have hempty : P.mCarrier = ∅ := Finset.eq_empty_iff_forall_not_mem.mpr
      (fun m hm => hne ⟨m, hm⟩)
    rw [restrictedPacketSum_zero_of_mCarrier_empty P hempty a b k,
      maxShiftedPacketNorm_zero_of_mCarrier_empty P hempty k (physicalPeriod P)]
    simp only [norm_zero, mul_zero, le_refl]

/-- The corresponding exact C² log² loss with ONE common frequency maximum. -/
theorem actual_same_mask_physical_norm_sq (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) :
    ‖completedPacketSum (restrictM P a b) k‖^2 ≤
      physicalCompletionConstant^2 * (Real.log (2 + P.V))^2 *
        maxShiftedPacketNormSq P k (physicalPeriod P) := by
  have hnorm := actual_same_mask_physical_norm P a b k
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simpa only [mul_pow, maxShiftedPacketNorm_sq] using hsquare

end
end ImbalancedChen.Part3.ActualCommonIntervalPhysicalLogBudgetSourceOnly
