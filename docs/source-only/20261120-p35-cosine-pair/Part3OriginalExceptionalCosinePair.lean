import ImbalancedChen.Part3OriginalAllChartLossyPair
import ImbalancedChen.Part3OriginalPositiveMarkOrder
import ImbalancedChen.Part3ActualPositiveNativeDiagonal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Pay the actual exceptional cosine denominator on the reduced n-side
pair. High-order slots vanish in the original common positive m row;
the remaining slots have a uniform positive cosine lower bound. This
does not establish the 7/32 gap, sharp J, or the raw oldclass return.
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalExceptionalCosinePair20261120
open Finset
open scoped BigOperators MatrixGroups Classical
open ActualFullCuspEigenbasis20261026b
open ActualCuspBasisWhittakerCoefficients20261102
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZSourceAssembly20261102 OriginalNativeCuspFunctionals20261102
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau mem_exceptional)
open OriginalExceptionalPostRemovalPair20261113
open OriginalAllChartLossyPair20261119 (transportedPrice all_chart_pair_with_transport)
open OriginalPositiveMarkOrder20261113 (high_positive_zero)
open ActualPositiveNativeDiagonal20261112 (complementaryHeight complementary_range)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold)
open P3NativePeriod64SamplingSourceOnly (D4)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- A fixed positive constant; no numerical spectral-gap input enters. -/
def cosineCost : ℝ := 1/Real.cos (3*Real.pi/8)

theorem cosineCost_pos : 0 < cosineCost := by
  have hp := Real.pi_pos
  have hc : 0 < Real.cos (3*Real.pi/8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hp], by linarith only [hp]⟩
  exact div_pos zero_lt_one hc

/-- The scalar bound on the retained interval, with the exact half-order
convention tau=2*sqrt(1/4-lambda). -/
theorem cosine_inverse_le_cost {t : ℝ} (h0 : 0 ≤ t) (hhi : t ≤ 3/4) :
    1/Real.cos (Real.pi*t/2) ≤ cosineCost := by
  have hp := Real.pi_pos
  have hc : 0 < Real.cos (3*Real.pi/8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hp], by linarith only [hp]⟩
  have ht0 : 0 ≤ Real.pi*t/2 := by positivity
  have hthi : Real.pi*t/2 ≤ 3*Real.pi/8 := by
    have h := mul_nonneg hp.le (sub_nonneg.mpr hhi)
    nlinarith only [h]
  have hcos : Real.cos (3*Real.pi/8) ≤ Real.cos (Real.pi*t/2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi ht0 (by linarith only [hp]) hthi
  have htpos : 0 < Real.cos (Real.pi*t/2) := hc.trans_le hcos
  unfold cosineCost
  apply (div_le_div_iff₀ htpos hc).mpr
  nlinarith only [hcos]

/-- The actual strict exceptional slot has a positive denominator. Its
value is the existing native complementary-height cosine. -/
theorem native_cosine_pos (z : ℕ+) (i : ↥(exceptional z)) :
    0 < Real.cos (Real.pi * tau z i.val / 2) := by
  have hc := (complementary_range z.val ((mem_exceptional z i.val).mp i.property).2).2.2
  have hid : Real.pi * tau z i.val / 2 = Real.pi * complementaryHeight z.val i.val := by
    unfold tau complementaryHeight
    ring
  rw [hid]
  exact hc

/-- Every high-order slot has zero m functional on the actual clipped
positive Poisson block, including an empty block or its endpoint. -/
theorem original_m_zero_high (z : ℕ+) (i : ↥(exceptional z))
    (hhigh : 3/4 < tau z i.val) (J j : ℕ) (ell : D4 → ℤ) :
    originalMFunctional J j ell z.val z.property i.val = 0 := by
  classical
  unfold originalMFunctional
  apply Finset.sum_eq_zero
  intro p hp
  have hp0 : 0 < p :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0:ℕ)<2) j) (Finset.mem_Ico.mp hp).1
  have hz := high_positive_zero z ⟨p,hp0⟩ i hhigh
  simp only [hz, mul_zero]

/-- Denominator payment for the same physical slots and original pair.
No assertion about all eigenvalues or a Kim--Sarnak gap is made. -/
theorem cosine_pair_le (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) :
    let F := mFactor D k upper J j ell
    let G := nFactor D r k upper negativeM ell
    (∑ a : Slots D k upper, (F a*G a)/Real.cos (Real.pi*tau a.1.val a.2.val/2)) ≤
      cosineCost * ∑ a : Slots D k upper, F a*G a := by
  classical
  let F := mFactor D k upper J j ell
  let G := nFactor D r k upper negativeM ell
  have hslot (a : Slots D k upper) :
      (F a*G a)/Real.cos (Real.pi*tau a.1.val a.2.val/2) ≤ cosineCost*(F a*G a) := by
    by_cases high : (3/4:ℝ) < tau a.1.val a.2.val
    · have hz : F a = 0 := by
        dsimp only [F, mFactor]
        rw [original_m_zero_high a.1.val a.2 high J j ell]
        simp
      simp only [hz, zero_mul, zero_div, mul_zero, le_refl]
    · have ht : 0 ≤ tau a.1.val a.2.val := by unfold tau; positivity
      have hc := cosine_inverse_le_cost ht (le_of_not_gt high)
      have hfg : 0 ≤ F a*G a := by dsimp [F,G,mFactor,nFactor]; positivity
      calc
        _ = (1/Real.cos (Real.pi*tau a.1.val a.2.val/2))*(F a*G a) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hc hfg
  calc
    _ ≤ ∑ a : Slots D k upper, cosineCost*(F a*G a) := Finset.sum_le_sum (fun a _ => hslot a)
    _ = _ := by rw [Finset.mul_sum]

/-- The cosine denominator is paid in the existing all-chart reduced
pair bound, with the prior explicit 3/4 transport price unchanged. -/
theorem cosine_pair_with_transport {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
      (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ),
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    let W := threshold V Z
    let F := mFactor D k upper J j ell
    let G := nFactor D r k upper negativeM ell
    (∑ a : Slots D k upper, (F a*G a)/Real.cos (Real.pi*tau a.1.val a.2.val/2))^2 ≤
      cosineCost^2 *
      (((2+Real.log (4*V+1))^2 *
        ((transportedPrice C ε (Z/2) M W + transportedPrice C ε Z M W)/4)) *
      ((4*sieveConstant*(1+rowLength k/Z))*
        ∑ z : ↥(levels D k upper), rowMass D r k z.val)) := by
  obtain ⟨C, cp, hpair⟩ := all_chart_pair_with_transport hε
  refine ⟨C, cp, ?_⟩
  intro D r k upper negativeM J j ell
  dsimp only
  let F := mFactor D k upper J j ell
  let G := nFactor D r k upper negativeM ell
  have hw : 0 ≤ ∑ a : Slots D k upper,
      (F a*G a)/Real.cos (Real.pi*tau a.1.val a.2.val/2) := by
    apply Finset.sum_nonneg
    intro a _
    apply div_nonneg
    · dsimp [F,G,mFactor,nFactor]; positivity
    · exact (native_cosine_pos a.1.val a.2).le
  have hb := cosine_pair_le D r k upper negativeM J j ell
  have hs := pow_le_pow_left₀ hw hb 2
  calc
    _ ≤ (cosineCost * ∑ a : Slots D k upper, F a*G a)^2 := hs
    _ = cosineCost^2 * (∑ a : Slots D k upper, F a*G a)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpair D r k upper negativeM J j ell) (sq_nonneg _)

end ImbalancedChen.Part3.OriginalExceptionalCosinePair20261120
end
