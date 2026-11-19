import ImbalancedChen.Part3OriginalRawChartSieve
import ImbalancedChen.Part3ActualPrescribedTraceWeights
import ImbalancedChen.Part3OriginalPrescribedOppositeTrace

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
The actual opposite-sign K transform on the original strict-exceptional
chart, with same-phase m J sums and the unremoved fixed-level n cost. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalOppositeRawChart20261120
open Finset Set
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualFullCuspEigenbasis20261026b ActualCuspEigenbasisNativeLabels20261026b
open ActualCuspBasisWhittakerCoefficients20261102
open ActualUnitBandSpectralMass20261112 (order_exceptional)
open ActualOppositeBesselTransform20261112 (kTransform)
open ActualPrescribedTraceWeights20261112 (exceptional_bound)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalNativeCuspFunctionals20261102
open OriginalExceptionalJNativeCompletion20261110
  (exceptional mem_exceptional tau clippedJ classicalLevels pascadiJ original_chart_J_one_phase)
open OriginalExceptionalPostRemovalPair20261113 (levels Slots rowMass rowLength mFactor)
open OriginalPositiveProfileBudget20261120 (inverseWeightedRawN)
open OriginalRawChartSieve20261120 (inverse_raw_energy_le)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- The actual opposite-sign discrete trace slot, before oldform removal. -/
def oppositeRawSlot (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (Y : ℝ)
    (a : Slots D k upper) : ℂ :=
  (8*kTransform (basisOrder a.1.val.val a.1.val.property a.2.val) (spectralTest ell Y)) *
    (star (originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val) *
      originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val)

/-- The exact K-transform exceptional branch, the original n row and
one common m phase. The K budget is chosen before the level, residual
mark and sign, but is allowed to depend on ell and Y. -/
theorem opposite_chart_with_raw_sieve (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (D : OriginalData) (k : BlockKey) (upper : Bool) (J j : ℕ),
    D.block.atom.residue ≠ 0 →
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
    let W := threshold V Z
    ∃ ω : ℝ,
      ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool),
      traceNegative D k negativeM = true →
      (∑ a : Slots D k upper, ‖oppositeRawSlot D r k upper negativeM J j ell Y a‖)^2 ≤
        B^2 * (((2+Real.log (4*V+1))^2 *
          ((pascadiJ (classicalLevels (Z/2)) W j ω +
            pascadiJ (classicalLevels Z) W j ω)/4)) *
          ((2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/Z)) *
            ∑ z : ↥(levels D k upper), rowMass D r k z.val)) := by
  classical
  obtain ⟨B, hB, hK⟩ := exceptional_bound ell hY
  refine ⟨B, hB, ?_⟩
  intro D k upper J j ha
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
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
  intro r negativeM hs
  let H := inverseWeightedRawN D r k upper negativeM j ell
  have hpoint (a : Slots D k upper) :
      ‖oppositeRawSlot D r k upper negativeM J j ell Y a‖ ≤
        B * (‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
          ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖) := by
    have hx := ((mem_exceptional a.1.val a.2.val).mp a.2.property).2
    obtain ⟨α, hα, horder⟩ := order_exceptional a.1.val.val hx
    have hk := (hK α hα).2
    unfold oppositeRawSlot
    rw [norm_mul,norm_mul,norm_star,horder]
    exact mul_le_mul_of_nonneg_right hk (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsum : (∑ a : Slots D k upper, ‖oppositeRawSlot D r k upper negativeM J j ell Y a‖) ≤
      B * ∑ a : Slots D k upper,
        ‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
        ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖ := by
    calc
      _ ≤ ∑ a : Slots D k upper, B *
          (‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
            ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖) :=
        Finset.sum_le_sum (fun a _ => hpoint a)
      _ = _ := by rw [Finset.mul_sum]
  have hsplit : (∑ a : Slots D k upper,
      ‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
      ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖) =
      ∑ a : Slots D k upper, F a * H a := by
    apply Finset.sum_congr rfl
    intro a _
    have hp : 0 < Real.sqrt (W ^ tau a.1.val a.2.val) :=
      Real.sqrt_pos.2 (Real.rpow_pos_of_pos hW _)
    dsimp only [F,H,mFactor,inverseWeightedRawN,W,V,Z]
    field_simp [hp.ne'] <;> ring
  have hnon : 0 ≤ ∑ a : Slots D k upper, ‖oppositeRawSlot D r k upper negativeM J j ell Y a‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq := pow_le_pow_left₀ hnon hsum 2
  have hm0 : 0 ≤ ∑ a : Slots D k upper, (F a)^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hn0 : 0 ≤ ∑ a : Slots D k upper, (H a)^2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hN := inverse_raw_energy_le D r k upper negativeM j ell ha
  have henergy := (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F H).trans
    (mul_le_mul hm hN hn0 (hm0.trans hm))
  calc
    _ ≤ (B * ∑ a : Slots D k upper,
        ‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
        ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖)^2 := hsq
    _ = B^2 * (∑ a : Slots D k upper, F a*H a)^2 := by rw [hsplit,mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy (sq_nonneg _)

end ImbalancedChen.Part3.OriginalOppositeRawChart20261120
end
