import ImbalancedChen.Part3OriginalExceptionalCosinePair
import ImbalancedChen.Part3OriginalMarkedPacketLimits

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.  Pointwise bridge for the
strict exceptional part of the original positive trace.  The n row is
the actual level-dependent row, not a common sequence.
-/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveRawCosine20261120
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualFullCuspEigenbasis20261026b
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalNativeCuspFunctionals20261102
open OriginalExceptionalJNativeCompletion20261110 (exceptional mem_exceptional tau)
open OriginalExceptionalCosinePair20261120
open ActualPositiveNativeDiagonal20261112 (nativeWeight complementaryHeight)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- The actual complex positive-trace slot, before oldform removal. -/
theorem raw_positive_slot_cosine_bound
    (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (Y : ℝ)
    (z : ℕ+) (i : ↥(exceptional z)) :
    ‖nativeWeight z.val (spectralTest ell Y) i.val *
      (star (originalMFunctional J j ell z.val z.property i.val) *
        originalNFunctional D r k upper negativeM ell z.val z.property i.val)‖ ≤
      cosineCost * ‖exceptionalWeight (spectralTest ell Y) (complementaryHeight z.val i.val)‖ *
        ‖originalMFunctional J j ell z.val z.property i.val‖ *
        ‖originalNFunctional D r k upper negativeM ell z.val z.property i.val‖ := by
  classical
  by_cases high : (3/4 : ℝ) < tau z i.val
  · rw [original_m_zero_high z i high J j ell]
    simp
  · have ht : 0 ≤ tau z i.val := by unfold tau; positivity
    have hb := cosine_inverse_le_cost ht (le_of_not_gt high)
    have hp := native_cosine_pos z i
    have hid : Real.pi * complementaryHeight z.val i.val = Real.pi * tau z i.val / 2 := by
      unfold tau complementaryHeight
      ring
    have hc : 0 ≤ Real.cos (Real.pi * complementaryHeight z.val i.val) := by
      rw [hid]
      exact hp.le
    rw [nativeWeight, if_pos ((mem_exceptional z i.val).mp i.property).2]
    simp only [norm_mul, norm_div, norm_star, Complex.norm_real,
      Real.norm_of_nonneg hc, hid]
    have hnonneg : 0 ≤
        ‖exceptionalWeight (spectralTest ell Y) (complementaryHeight z.val i.val)‖ *
        (‖originalMFunctional J j ell z.val z.property i.val‖ *
          ‖originalNFunctional D r k upper negativeM ell z.val z.property i.val‖) := by positivity
    calc
      _ = (1 / Real.cos (Real.pi * tau z i.val / 2)) *
          (‖exceptionalWeight (spectralTest ell Y) (complementaryHeight z.val i.val)‖ *
            (‖originalMFunctional J j ell z.val z.property i.val‖ *
              ‖originalNFunctional D r k upper negativeM ell z.val z.property i.val‖)) := by ring
      _ ≤ cosineCost *
          (‖exceptionalWeight (spectralTest ell Y) (complementaryHeight z.val i.val)‖ *
            (‖originalMFunctional J j ell z.val z.property i.val‖ *
              ‖originalNFunctional D r k upper negativeM ell z.val z.property i.val‖)) :=
        mul_le_mul_of_nonneg_right hb hnonneg
      _ = _ := by ring

end ImbalancedChen.Part3.OriginalPositiveRawCosine20261120
end
