import ImbalancedChen.Part3ActualCommonIntervalCompletion
import ImbalancedChen.Part3IntervalHarmonicPairBound
import ImbalancedChen.Part3IntervalFourierChordLower
import Mathlib.Tactic

namespace ImbalancedChen.Part3.ActualCommonIntervalCompletionL1SourceOnly
noncomputable section

open Classical
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionSourceOnly
open ImbalancedChen.Part3.ActualIntervalGeometricSumSourceOnly
open ImbalancedChen.Part3.IntervalFourierChordLowerSourceOnly
open ImbalancedChen.Part3.IntervalHarmonicPairBoundSourceOnly

variable {ι : Type*}

/-- Clamp a reversed interval to the same empty interval, only for the
ordered-endpoint interface of the geometric-sum supplier. -/
def completionLo (P : PacketData ι) (a b : ℕ) : ℕ :=
  min (max P.lo a) (min P.hi b)

def completionHi (P : PacketData ι) (_a b : ℕ) : ℕ := min P.hi b

theorem completionLo_le_hi (P : PacketData ι) (a b : ℕ) :
    completionLo P a b ≤ completionHi P a b := by
  exact min_le_right _ _

theorem commonInterval_eq_Ico (P : PacketData ι) (a b : ℕ) :
    commonInterval P a b = Finset.Ico (completionLo P a b) (completionHi P a b) := by
  ext m
  simp only [commonInterval, PacketData.mCarrier, completionLo, completionHi,
    Finset.mem_inter, Finset.mem_Ico]
  omega

theorem sum_zmod_val_reindex (N : ℕ) [NeZero N] (f : ℕ → ℂ) :
    (∑ r : ZMod N, f r.val) = ∑ m ∈ Finset.range N, f m := by
  refine Finset.sum_bij' (fun r _hr => r.val) (fun m _hm => (m : ZMod N))
    (fun r _hr => ?_) (fun m _hm => ?_) (fun r _hr => ?_)
    (fun m hm => ?_) (fun _r _hr => rfl)
  · exact Finset.mem_range.mpr (ZMod.val_lt r)
  · exact Finset.mem_univ _
  · exact ZMod.natCast_zmod_val r
  · exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hm)

/-- The actual DFT of the actual common mask, as a finite interval sum. -/
theorem finiteFourierCoeff_interval (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (hperiod : P.hi < N) (r : ZMod N) :
    finiteFourierCoeff P a b N r =
      ∑ m ∈ Finset.Ico (completionLo P a b) (completionHi P a b),
        ZMod.stdAddChar (-((m : ZMod N) * r)) := by
  have hfilter : (Finset.range N).filter (fun m => m ∈ commonInterval P a b) =
      commonInterval P a b := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · exact fun hm => hm.2
    · intro hm
      have hmhi : m < P.hi :=
        (Finset.mem_Ico.mp (Finset.mem_inter.mp hm).2).2
      exact ⟨Finset.mem_range.mpr (lt_trans hmhi hperiod), hm⟩
  rw [finiteFourierCoeff_eq_sum]
  calc
    (∑ x : ZMod N, ZMod.stdAddChar (-(x * r)) * cyclicIndicator P a b N x) =
        ∑ x : ZMod N, if x.val ∈ commonInterval P a b then
          ZMod.stdAddChar (-((x.val : ZMod N) * r)) else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : x.val ∈ commonInterval P a b <;>
        simp [cyclicIndicator, hx, ZMod.natCast_zmod_val]
    _ = ∑ m ∈ Finset.range N, if m ∈ commonInterval P a b then
          ZMod.stdAddChar (-((m : ZMod N) * r)) else 0 :=
      sum_zmod_val_reindex N (fun m => if m ∈ commonInterval P a b then
        ZMod.stdAddChar (-((m : ZMod N) * r)) else 0)
    _ = ∑ m ∈ (Finset.range N).filter (fun m => m ∈ commonInterval P a b),
          ZMod.stdAddChar (-((m : ZMod N) * r)) := by
      rw [Finset.sum_filter]
    _ = _ := by rw [hfilter, commonInterval_eq_Ico]

def normalizedFourierCoeff (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (r : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * finiteFourierCoeff P a b N r

theorem normalizedFourierCoeff_norm (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (r : ZMod N) :
    ‖normalizedFourierCoeff P a b N r‖ = ‖finiteFourierCoeff P a b N r‖ / (N : ℝ) := by
  rw [normalizedFourierCoeff, norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv]
  ring

theorem normalizedFourierCoeff_zero_bound (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hperiod : P.hi < N) :
    ‖normalizedFourierCoeff P a b N 0‖ ≤ 1 := by
  have hcoef : finiteFourierCoeff P a b N 0 =
      ((completionHi P a b - completionLo P a b : ℕ) : ℂ) := by
    rw [finiteFourierCoeff_interval P a b N hperiod 0]
    simp [Nat.card_Ico]
  have hlen : completionHi P a b - completionLo P a b ≤ N := by
    exact le_trans (Nat.sub_le _ _)
      (le_trans (min_le_left P.hi b) (Nat.le_of_lt hperiod))
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le P.hi) hperiod)
  rw [normalizedFourierCoeff_norm, hcoef, Complex.norm_natCast]
  apply (div_le_iff₀ hNpos).mpr
  simpa only [one_mul] using (show
    ((completionHi P a b - completionLo P a b : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast hlen)

/-- The negative DFT frequency has the positive representative N-r.val.
Thus the actual chord supplier applies without changing its constants. -/
theorem normalizedFourierCoeff_nonzero_bound (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hN : 2 ≤ N) (hperiod : P.hi < N)
    (r : ZMod N) (hr0 : r ≠ 0) :
    ‖normalizedFourierCoeff P a b N r‖ ≤
      (1 : ℝ) / (2 * ((min r.val (N - r.val) : ℕ) : ℝ)) := by
  let s : ℕ := N - r.val
  have hrval0 : r.val ≠ 0 := fun hz => hr0 ((ZMod.val_eq_zero r).mp hz)
  have hrvalN := ZMod.val_lt r
  have hs1 : 1 ≤ s := by dsimp [s]; omega
  have hsN : s < N := by dsimp [s]; omega
  have hsCast : (s : ZMod N) = -r := by
    dsimp [s]
    rw [Nat.cast_sub (Nat.le_of_lt hrvalN), ZMod.natCast_self,
      ZMod.natCast_zmod_val, zero_sub]
  have hmin : min s (N - s) = min r.val (N - r.val) := by
    dsimp [s]
    omega
  have hphase (m : ℕ) : ZMod.stdAddChar (-((m : ZMod N) * r)) =
      phaseAt ((s : ℝ) / (N : ℝ)) m := by
    have hc : -((m : ZMod N) * r) = (s : ZMod N) * (m : ZMod N) := by
      rw [hsCast]
      ring
    rw [hc, cyclicCharacter_eq_exp, ZMod.val_natCast_of_lt hsN]
    unfold phaseAt
    push_cast
    congr 1
    ring
  have hsum : finiteFourierCoeff P a b N r =
      ∑ m ∈ Finset.Ico (completionLo P a b) (completionHi P a b),
        phaseAt ((s : ℝ) / (N : ℝ)) m := by
    rw [finiteFourierCoeff_interval P a b N hperiod r]
    apply Finset.sum_congr rfl
    intro m _hm
    exact hphase m
  rw [normalizedFourierCoeff_norm, hsum]
  have hbound := normalized_interval_fourier_coeff_bound N s
    (completionLo P a b) (completionHi P a b) hN hs1 hsN (completionLo_le_hi P a b)
  have hden := (le_min_iff.mp hbound).2
  simpa only [hmin] using hden

/-- Actual common-interval completion L1 bound, with all normalizations fixed.
Only the elementary period gates are inputs; no coefficient bound is assumed. -/
theorem actual_common_interval_completion_l1 (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hN : 2 ≤ N) (hperiod : P.hi < N) :
    (∑ r : ZMod N, ‖normalizedFourierCoeff P a b N r‖) ≤ 2 + Real.log N := by
  exact cyclic_coefficient_l1_le_two_add_log N hN (normalizedFourierCoeff P a b N)
    (normalizedFourierCoeff_zero_bound P a b N hperiod)
    (normalizedFourierCoeff_nonzero_bound P a b N hN hperiod)

/-- The coefficients just bounded are exactly those in the actual packet
completion, including the inverse-N factor. -/
theorem completedPacketSum_normalized_completion (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hperiod : P.hi < N) (k : D4 → ℤ) :
    completedPacketSum (restrictM P a b) k =
      ∑ r : ZMod N, normalizedFourierCoeff P a b N r * shiftedPacketSum P k N r := by
  rw [completedPacketSum_common_completion P a b N hperiod k]
  simp only [normalizedFourierCoeff, Finset.mul_sum, mul_assoc]

end
end ImbalancedChen.Part3.ActualCommonIntervalCompletionL1SourceOnly
