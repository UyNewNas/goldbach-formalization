import ImbalancedChen.Part3OriginalExceptionalPostRemovalPair
import ImbalancedChen.Part3OriginalMarkedPacketLimits

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Finite same-chart Cauchy reduction for the raw same-sign exceptional
trace. The transform stays in the genuinely level-dependent n energy.
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveRawCauchy20261120
open Finset
open scoped BigOperators MatrixGroups Classical
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalNativeCuspFunctionals20261102
open OriginalExceptionalJNativeCompletion20261110 (tau clippedJ classicalLevels pascadiJ original_chart_J_one_phase)
open OriginalExceptionalPostRemovalPair20261113 (Slots levels mFactor)
open ActualPositiveNativeDiagonal20261112 (nativeWeight)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- One actual exceptional slot of the positive trace, before removal. -/
def rawSlot (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (Y : ℝ)
    (a : Slots D k upper) : ℂ :=
  nativeWeight a.1.val.val (spectralTest ell Y) a.2.val *
    (star (originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val) *
      originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val)

/-- The raw n row carries the actual transform and the inverse m weight.
It is indexed by both the level and the native basis vector. -/
def rawNFactor (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (j : ℕ) (ell : D4 → ℤ) (Y : ℝ)
    (a : Slots D k upper) : ℝ :=
  (‖nativeWeight a.1.val.val (spectralTest ell Y) a.2.val‖ *
    ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖) /
      Real.sqrt ((threshold (((2:ℕ)^j : ℕ) : ℝ) (fixedZ D upper)) ^ tau a.1.val a.2.val)

/-- Exact square-root split: no bound on the n row or Bessel transform. -/
theorem raw_slot_factorization (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    (Y : ℝ) (a : Slots D k upper) :
    ‖rawSlot D r k upper negativeM J j ell Y a‖ =
      mFactor D k upper J j ell a * rawNFactor D r k upper negativeM j ell Y a := by
  have hw : 0 < threshold (((2:ℕ)^j : ℕ) : ℝ) (fixedZ D upper) :=
    threshold_pos (by positivity)
  have hs : 0 < Real.sqrt
      ((threshold (((2:ℕ)^j : ℕ) : ℝ) (fixedZ D upper)) ^ tau a.1.val a.2.val) :=
    Real.sqrt_pos.2 (Real.rpow_pos_of_pos hw _)
  rw [rawSlot, norm_mul, norm_mul, norm_star]
  unfold mFactor rawNFactor
  field_simp [hs.ne'] <;> ring

/-- A single phase bounds the original m energy on both endpoint-correct
level ranges. The exact raw n energy and native spectral weight are not
replaced by their post-removal analogues. -/
theorem raw_positive_chart_to_pascadi (D : OriginalData)
    (k : BlockKey) (upper : Bool) (J j : ℕ) (ell : D4 → ℤ) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let W := threshold V Z
    ∃ ω : ℝ, ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool) (Y : ℝ),
      (∑ a : Slots D k upper, ‖rawSlot D r k upper negativeM J j ell Y a‖)^2 ≤
      ((2 + Real.log (4*V+1))^2 *
        ((pascadiJ (classicalLevels (Z/2)) W j ω +
          pascadiJ (classicalLevels Z) W j ω)/4)) *
      ∑ a : Slots D k upper, (rawNFactor D r k upper negativeM j ell Y a)^2 := by
  classical
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let W := threshold V Z
  let F := mFactor D k upper J j ell
  have hW : 0 < W := threshold_pos (show 0 < V by dsimp [V]; positivity)
  have mSq : (∑ a : Slots D k upper, (F a)^2) = clippedJ (levels D k upper) W J j ell := by
    rw [Fintype.sum_sigma]
    simp only [F,mFactor,W,V,Z,mul_pow,Real.sq_sqrt (Real.rpow_nonneg hW.le _),
      clippedJ,Finset.univ_eq_attach,Finset.sum_attach]
  obtain ⟨ω, hm⟩ := original_chart_J_one_phase D k upper hW J j ell
  rw [← mSq] at hm
  refine ⟨ω, ?_⟩
  intro r negativeM Y
  let G := rawNFactor D r k upper negativeM j ell Y
  have hs : (∑ a : Slots D k upper, ‖rawSlot D r k upper negativeM J j ell Y a‖) =
      ∑ a : Slots D k upper, F a * G a := by
    apply Finset.sum_congr rfl
    intro a _
    exact raw_slot_factorization D r k upper negativeM J j ell Y a
  rw [hs]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G).trans
    (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg (fun a _ => sq_nonneg (G a))))

end ImbalancedChen.Part3.OriginalPositiveRawCauchy20261120
end
