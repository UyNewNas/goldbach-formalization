import ImbalancedChen.Part3ActualCommonMask
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

namespace ImbalancedChen.Part3.ActualCommonIntervalCompletionSourceOnly
noncomputable section

open Classical
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3 (CommonCompletedVariable)
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly

variable {ι : Type*}

def commonInterval (P : PacketData ι) (a b : ℕ) : Finset ℕ :=
  Finset.Ico a b ∩ P.mCarrier

/-- A single cyclic indicator, fixed before all row and level sums. -/
def cyclicIndicator (P : PacketData ι) (a b N : ℕ) (x : ZMod N) : ℂ :=
  if x.val ∈ commonInterval P a b then 1 else 0

def finiteFourierCoeff (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (r : ZMod N) : ℂ :=
  ZMod.dft (cyclicIndicator P a b N) r

theorem finiteFourierCoeff_eq_sum (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (r : ZMod N) :
    finiteFourierCoeff P a b N r =
      ∑ x : ZMod N, ZMod.stdAddChar (-(x * r)) * cyclicIndicator P a b N x := by
  rw [finiteFourierCoeff, ZMod.dft_apply]
  simp only [smul_eq_mul]

theorem cyclicIndicator_nat (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (hN : P.hi < N) (m : ℕ) (hm : m < P.hi) :
    cyclicIndicator P a b N (m : ZMod N) =
      if m ∈ commonInterval P a b then (1 : ℂ) else 0 := by
  unfold cyclicIndicator
  rw [ZMod.val_natCast_of_lt (lt_trans hm hN)]

/-- Pinned mathlib inversion, with its negative-sign forward DFT convention. -/
theorem cyclicIndicator_inversion (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (x : ZMod N) :
    cyclicIndicator P a b N x =
      (N : ℂ)⁻¹ * ∑ r : ZMod N,
        finiteFourierCoeff P a b N r * ZMod.stdAddChar (r * x) := by
  have hinv := congrArg (fun g : ZMod N → ℂ => g x)
    ((ZMod.dft (N := N) (E := ℂ)).symm_apply_apply (cyclicIndicator P a b N))
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul] at hinv
  calc
    cyclicIndicator P a b N x =
        (N : ℂ)⁻¹ * ∑ r : ZMod N,
          ZMod.stdAddChar (r * x) * ZMod.dft (cyclicIndicator P a b N) r := hinv.symm
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _hr
      exact mul_comm _ _

theorem cyclicCharacter_eq_exp (N : ℕ) [NeZero N] (r : ZMod N) (m : ℕ) :
    ZMod.stdAddChar (r * (m : ZMod N)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r.val : ℂ) * (m : ℂ) / (N : ℂ)) := by
  have hc : r * (m : ZMod N) = ((r.val * m : ℕ) : ZMod N) := by
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hc, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  push_cast
  congr 1
  ring

/-- Exact indicator inversion on every actual natural point below P.hi. -/
theorem commonInterval_indicator_inversion (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hN : P.hi < N) (m : ℕ) (hm : m < P.hi) :
    (if m ∈ commonInterval P a b then (1 : ℂ) else 0) =
      (N : ℂ)⁻¹ * ∑ r : ZMod N,
        finiteFourierCoeff P a b N r *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r.val : ℂ) * (m : ℂ) / (N : ℂ)) := by
  rw [← cyclicIndicator_nat P a b N hN m hm, cyclicIndicator_inversion]
  simp only [cyclicCharacter_eq_exp]

/-- The r-th completion adds r/N to the SAME physical additive phase. -/
def shiftedCompleted (P : PacketData ι) (k : D4 → ℤ) (N : ℕ) (r : ZMod N) :
    CommonCompletedVariable :=
  { P.completed k with
    additivePhase := (P.completed k).additivePhase + (r.val : ℝ) / (N : ℝ) }

theorem shiftedCompleted_phase (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) (r : ZMod N) :
    (shiftedCompleted P k N r).additivePhase =
      (k 1 : ℝ) / (64 * P.V) + (r.val : ℝ) / (N : ℝ) := by rfl

theorem shiftedCompleted_weight (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) [NeZero N] (r : ZMod N) (m : ℕ) :
    (shiftedCompleted P k N r).weight m =
      (P.completed k).weight m * ZMod.stdAddChar (r * (m : ZMod N)) := by
  rw [cyclicCharacter_eq_exp]
  by_cases hm : m ∈ Finset.Ico P.lo P.hi
  · simp only [shiftedCompleted, PacketData.completed, CommonCompletedVariable.weight,
      if_pos hm]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [shiftedCompleted, PacketData.completed, CommonCompletedVariable.weight,
      if_neg hm, zero_mul]

def shiftedPacketSum (P : PacketData ι) (k : D4 → ℤ) (N : ℕ) (r : ZMod N) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    (shiftedCompleted P k N r).weight m *
      signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n

theorem shiftedPacketSum_common_phase (P : PacketData ι) (k : D4 → ℤ)
    (N : ℕ) (r : ZMod N) :
    shiftedPacketSum P k N r =
      (∑ m ∈ P.mCarrier, (shiftedCompleted P k N r).weight m) *
        (∑ j ∈ P.rows, ∑ n ∈ P.nCarrier j,
          signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n) := by
  unfold shiftedPacketSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact (Finset.sum_mul_sum P.mCarrier (P.nCarrier j)
    (fun m => (shiftedCompleted P k N r).weight m)
    (fun n => signedCoefficient P.negativeCusp
      (modePacket (P.packet j) k P.U P.Z) n)).symm

theorem commonMaskWeight_cyclic (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (hN : P.hi < N) (k : D4 → ℤ) (m : ℕ) (hm : m ∈ P.mCarrier) :
    commonMaskWeight P a b k m =
      cyclicIndicator P a b N (m : ZMod N) * (P.completed k).weight m := by
  have hhi : m < P.hi := (Finset.mem_Ico.mp hm).2
  rw [cyclicIndicator_nat P a b N hN m hhi]
  have hmem : m ∈ commonInterval P a b ↔ m ∈ Finset.Ico a b := by
    simp only [commonInterval, Finset.mem_inter, hm, and_true]
  rw [hmem]
  by_cases hI : m ∈ Finset.Ico a b <;> simp [commonMaskWeight, hI]

theorem commonMaskWeight_completion (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (hN : P.hi < N) (k : D4 → ℤ) (m : ℕ) (hm : m ∈ P.mCarrier) :
    commonMaskWeight P a b k m =
      (N : ℂ)⁻¹ * ∑ r : ZMod N,
        finiteFourierCoeff P a b N r * (shiftedCompleted P k N r).weight m := by
  rw [commonMaskWeight_cyclic P a b N hN k m hm, cyclicIndicator_inversion]
  calc
    ((N : ℂ)⁻¹ * ∑ r : ZMod N,
        finiteFourierCoeff P a b N r * ZMod.stdAddChar (r * (m : ZMod N))) *
          (P.completed k).weight m =
      (N : ℂ)⁻¹ * ∑ r : ZMod N,
        (finiteFourierCoeff P a b N r * ZMod.stdAddChar (r * (m : ZMod N))) *
          (P.completed k).weight m := by
      rw [mul_assoc, Finset.sum_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _hr
      rw [shiftedCompleted_weight]
      ring

theorem commonMask_msum_completion (P : PacketData ι) (a b N : ℕ) [NeZero N]
    (hN : P.hi < N) (k : D4 → ℤ) :
    (∑ m ∈ P.mCarrier, commonMaskWeight P a b k m) =
      (N : ℂ)⁻¹ * ∑ r : ZMod N,
        finiteFourierCoeff P a b N r *
          (∑ m ∈ P.mCarrier, (shiftedCompleted P k N r).weight m) := by
  calc
    (∑ m ∈ P.mCarrier, commonMaskWeight P a b k m) =
        ∑ m ∈ P.mCarrier, (N : ℂ)⁻¹ * ∑ r : ZMod N,
          finiteFourierCoeff P a b N r * (shiftedCompleted P k N r).weight m := by
      apply Finset.sum_congr rfl
      intro m hm
      exact commonMaskWeight_completion P a b N hN k m hm
    _ = (N : ℂ)⁻¹ * ∑ m ∈ P.mCarrier, ∑ r : ZMod N,
          finiteFourierCoeff P a b N r * (shiftedCompleted P k N r).weight m := by
      rw [Finset.mul_sum]
    _ = (N : ℂ)⁻¹ * ∑ r : ZMod N, ∑ m ∈ P.mCarrier,
          finiteFourierCoeff P a b N r * (shiftedCompleted P k N r).weight m := by
      rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.mul_sum]

/-- The ACTUAL restricted completedPacketSum is a finite sum of shared phase
shifts. Every original level, packet, n carrier and common m carrier remains. -/
theorem completedPacketSum_common_completion (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hN : P.hi < N) (k : D4 → ℤ) :
    completedPacketSum (restrictM P a b) k =
      (N : ℂ)⁻¹ * ∑ r : ZMod N,
        finiteFourierCoeff P a b N r * shiftedPacketSum P k N r := by
  rw [completedPacketSum_restrictM, maskedCompletedPacketSum_common_interval,
    commonMask_msum_completion P a b N hN k]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _hr
  rw [shiftedPacketSum_common_phase]
  ring

/-- Fully explicit positive-exponential version of the same actual identity. -/
theorem completedPacketSum_common_completion_exp (P : PacketData ι)
    (a b N : ℕ) [NeZero N] (hN : P.hi < N) (k : D4 → ℤ) :
    completedPacketSum (restrictM P a b) k =
      (N : ℂ)⁻¹ * ∑ r : ZMod N, finiteFourierCoeff P a b N r *
        (∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
          ((P.completed k).weight m *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r.val : ℂ) * (m : ℂ) / (N : ℂ))) *
          signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n) := by
  rw [completedPacketSum_common_completion P a b N hN k]
  simp only [shiftedPacketSum, shiftedCompleted_weight, cyclicCharacter_eq_exp]

end
end ImbalancedChen.Part3.ActualCommonIntervalCompletionSourceOnly
