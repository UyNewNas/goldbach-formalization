import ImbalancedChen.Part3ActualCommonIntervalCompletionL1
import Mathlib.Data.Finset.Lattice.Fold

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24. New source fragment.
Append after Part3ActualCommonIntervalCompletionL1.lean.txt; the companion
NormBundle candidate supplies that dependency and hoists the extra import.
The maximum is over ONE common frequency r applied to the complete packet,
including every original level. It is never a sum of separate level maxima.
-/

namespace ImbalancedChen.Part3.ActualCommonIntervalCompletionNormSourceOnly
noncomputable section

open Classical
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionL1SourceOnly

variable {ι : Type*}

/-- Maximum of the complete shifted packet norms, at one common frequency. -/
def maxShiftedPacketNorm (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) [NeZero N] : ℝ :=
  (Finset.univ : Finset (ZMod N)).sup' Finset.univ_nonempty
    (fun r => ‖shiftedPacketSum P k N r‖)

/-- The corresponding maximum of the complete shifted packet energies. -/
def maxShiftedPacketNormSq (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) [NeZero N] : ℝ :=
  (Finset.univ : Finset (ZMod N)).sup' Finset.univ_nonempty
    (fun r => ‖shiftedPacketSum P k N r‖^2)

theorem shiftedPacketNorm_le_max (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) [NeZero N] (r : ZMod N) :
    ‖shiftedPacketSum P k N r‖ ≤ maxShiftedPacketNorm P k N := by
  exact Finset.le_sup' (fun r => ‖shiftedPacketSum P k N r‖) (Finset.mem_univ r)

theorem shiftedPacketNormSq_le_max (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) [NeZero N] (r : ZMod N) :
    ‖shiftedPacketSum P k N r‖^2 ≤ maxShiftedPacketNormSq P k N := by
  exact Finset.le_sup' (fun r => ‖shiftedPacketSum P k N r‖^2) (Finset.mem_univ r)

theorem maxShiftedPacketNorm_nonneg (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) [NeZero N] : 0 ≤ maxShiftedPacketNorm P k N := by
  exact (norm_nonneg (shiftedPacketSum P k N 0)).trans (shiftedPacketNorm_le_max P k N 0)

theorem maxShiftedPacketNorm_attained (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) [NeZero N] :
    ∃ r : ZMod N, maxShiftedPacketNorm P k N = ‖shiftedPacketSum P k N r‖ := by
  rcases Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (ZMod N)).Nonempty)
      (fun r => ‖shiftedPacketSum P k N r‖) with ⟨r, _hr, heq⟩
  exact ⟨r, heq⟩

theorem maxShiftedPacketNorm_sq (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) [NeZero N] :
    (maxShiftedPacketNorm P k N)^2 = maxShiftedPacketNormSq P k N := by
  apply le_antisymm
  · rcases maxShiftedPacketNorm_attained P k N with ⟨r, hr⟩
    rw [hr]
    exact shiftedPacketNormSq_le_max P k N r
  · unfold maxShiftedPacketNormSq
    apply Finset.sup'_le
    intro r _hr
    exact pow_le_pow_left₀ (norm_nonneg _) (shiftedPacketNorm_le_max P k N r) 2

theorem completionLogFactor_nonneg (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ 2 + Real.log (N : ℝ) := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  linarith

/-- The actual mask cost: normalized cyclic coefficients multiply complete
packets at a common phase, so their L1 norm pays exactly one logarithm. -/
theorem actual_restrictedPacket_norm_le_completion_max (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hN : 2 ≤ N) (hperiod : P.hi < N) (k : D4 → ℤ) :
    ‖completedPacketSum (restrictM P a b) k‖ ≤
      (2 + Real.log N) * maxShiftedPacketNorm P k N := by
  rw [completedPacketSum_normalized_completion P a b N hperiod k]
  calc
    ‖∑ r : ZMod N, normalizedFourierCoeff P a b N r * shiftedPacketSum P k N r‖ ≤
        ∑ r : ZMod N, ‖normalizedFourierCoeff P a b N r * shiftedPacketSum P k N r‖ :=
      norm_sum_le _ _
    _ = ∑ r : ZMod N,
        ‖normalizedFourierCoeff P a b N r‖ * ‖shiftedPacketSum P k N r‖ := by
      simp only [norm_mul]
    _ ≤ ∑ r : ZMod N,
        ‖normalizedFourierCoeff P a b N r‖ * maxShiftedPacketNorm P k N := by
      apply Finset.sum_le_sum
      intro r _hr
      exact mul_le_mul_of_nonneg_left (shiftedPacketNorm_le_max P k N r) (norm_nonneg _)
    _ = (∑ r : ZMod N, ‖normalizedFourierCoeff P a b N r‖) *
        maxShiftedPacketNorm P k N := by rw [Finset.sum_mul]
    _ ≤ (2 + Real.log N) * maxShiftedPacketNorm P k N :=
      mul_le_mul_of_nonneg_right (actual_common_interval_completion_l1 P a b N hN hperiod)
        (maxShiftedPacketNorm_nonneg P k N)

/-- Squared completion cost, with the whole-packet maximum taken first. -/
theorem actual_restrictedPacket_norm_sq_le_completion_max_sq (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hN : 2 ≤ N) (hperiod : P.hi < N) (k : D4 → ℤ) :
    ‖completedPacketSum (restrictM P a b) k‖^2 ≤
      (2 + Real.log N)^2 * (maxShiftedPacketNorm P k N)^2 := by
  have hnorm := actual_restrictedPacket_norm_le_completion_max P a b N hN hperiod k
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Equivalent version with the maximum of actual squared packet norms. -/
theorem actual_restrictedPacket_norm_sq_le_completion_max_energy (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hN : 2 ≤ N) (hperiod : P.hi < N) (k : D4 → ℤ) :
    ‖completedPacketSum (restrictM P a b) k‖^2 ≤
      (2 + Real.log N)^2 * maxShiftedPacketNormSq P k N := by
  rw [← maxShiftedPacketNorm_sq]
  exact actual_restrictedPacket_norm_sq_le_completion_max_sq P a b N hN hperiod k

end
end ImbalancedChen.Part3.ActualCommonIntervalCompletionNormSourceOnly
