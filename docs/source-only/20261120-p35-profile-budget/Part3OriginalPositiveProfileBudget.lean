import ImbalancedChen.Part3OriginalPositiveRawCosine
import ImbalancedChen.Part3OriginalPositiveRawCauchy
import ImbalancedChen.Part3ActualPositiveCosineProfile

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
An explicit actual-test L1 budget for the numerator of the same-sign
complementary transform. It is not uniform in the test scale or mark.
-/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveProfileBudget20261120
open Set MeasureTheory Finset
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveCosineProfile20261112 (profile weighted_profile_L1)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight exceptional_transform)
open ActualPositiveNativeDiagonal20261112 (complementaryHeight complementary_range)
open OriginalExceptionalJNativeCompletion20261110 (exceptional mem_exceptional tau clippedJ classicalLevels pascadiJ original_chart_J_one_phase)
open OriginalExceptionalCosinePair20261120 (cosineCost cosineCost_pos)
open OriginalPositiveRawCosine20261120 (raw_positive_slot_cosine_bound)
open OriginalPositiveRawCauchy20261120 (rawSlot)
open OriginalExceptionalPostRemovalPair20261113 (Slots levels mFactor)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)
open OriginalNativeCuspFunctionals20261102
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- The exact real half-line norm of the given test's cosine profile. -/
def profileBudget (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) : ℝ :=
  8 * ∫ u in Ioi (0:ℝ), Real.cosh u * ‖profile ell hY u‖

theorem profileBudget_nonneg (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    0 ≤ profileBudget ell hY := by
  unfold profileBudget
  exact mul_nonneg (by norm_num) (integral_nonneg fun u =>
    mul_nonneg (Real.cosh_pos u).le (norm_nonneg _))

/-- Uniform over the actual complementary order, with the actual 8 and
the original test, without a numerical spectral-gap hypothesis. -/
theorem actual_numerator_le_profileBudget (ell : D4 → ℤ) {Y a : ℝ}
    (hY : 0 < Y) (ha : 0 ≤ a) (ha1 : a < 1/2) :
    ‖exceptionalWeight (spectralTest ell Y) a‖ ≤ profileBudget ell hY := by
  have hdom : ∀ᵐ u ∂volume.restrict (Ioi (0:ℝ)),
      ‖(Real.cosh (2*a*u):ℂ)*profile ell hY u‖ ≤
        Real.cosh u * ‖profile ell hY u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    have harg : |2*a*u| ≤ |u| := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg hu0]
      have h := mul_le_mul_of_nonneg_right (show 2*a ≤ 1 by linarith) hu0
      nlinarith only [h]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.cosh_pos _).le]
    exact mul_le_mul_of_nonneg_right (Real.cosh_le_cosh.mpr harg) (norm_nonneg _)
  have hI := norm_integral_le_of_norm_le (weighted_profile_L1 ell hY).integrableOn hdom
  rw [(exceptional_transform ell hY ha ha1).2,norm_mul]
  norm_num only [Complex.norm_ofNat]
  change 8 * ‖∫ u in Ioi (0:ℝ), (Real.cosh (2*a*u):ℂ)*profile ell hY u‖ ≤
    8 * ∫ u in Ioi (0:ℝ), Real.cosh u * ‖profile ell hY u‖
  exact mul_le_mul_of_nonneg_left hI (by norm_num)

/-- The bound applies to the literal raw product and all strict
exceptional slots; high-order slots are zero only on the m side. -/
theorem raw_slot_le_profileBudget (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    {Y : ℝ} (hY : 0 < Y) (z : ℕ+) (i : ↥(exceptional z)) :
    ‖ActualPositiveNativeDiagonal20261112.nativeWeight z.val (spectralTest ell Y) i.val *
      (star (originalMFunctional J j ell z.val z.property i.val) *
        originalNFunctional D r k upper negativeM ell z.val z.property i.val)‖ ≤
      cosineCost * profileBudget ell hY *
        ‖originalMFunctional J j ell z.val z.property i.val‖ *
        ‖originalNFunctional D r k upper negativeM ell z.val z.property i.val‖ := by
  have hr := complementary_range z.val ((mem_exceptional z i.val).mp i.property).2
  have hb := actual_numerator_le_profileBudget ell hY hr.1.le hr.2.1
  refine (raw_positive_slot_cosine_bound D r k upper negativeM J j ell Y z i).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left hb cosineCost_pos.le

/-- The same explicit budget applies simultaneously to every original
level and strict exceptional index of one physical chart. -/
theorem raw_chart_le_profileBudget (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    (∑ a : Slots D k upper, ‖rawSlot D r k upper negativeM J j ell Y a‖) ≤
      (cosineCost * profileBudget ell hY) *
        ∑ a : Slots D k upper,
          ‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
          ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖ := by
  calc
    _ ≤ ∑ a : Slots D k upper,
        (cosineCost * profileBudget ell hY) *
          (‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
            ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [rawSlot,mul_assoc] using
        raw_slot_le_profileBudget D r k upper negativeM J j ell hY a.1.val a.2
    _ = _ := by rw [Finset.mul_sum]

/-- Raw n norm with exactly the reciprocal of the m-side J weight. -/
def inverseWeightedRawN (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (j : ℕ) (ell : D4 → ℤ)
    (a : Slots D k upper) : ℝ :=
  ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖ /
    Real.sqrt ((threshold (((2:ℕ)^j : ℕ) : ℝ) (fixedZ D upper)) ^ tau a.1.val a.2.val)

/-- Full original positive exceptional chart: the test's explicit L1
budget and the same two J intervals precede a genuine raw n energy. -/
theorem raw_chart_profile_to_pascadi (D : OriginalData) (k : BlockKey)
    (upper : Bool) (J j : ℕ) (ell : D4 → ℤ) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let W := threshold V Z
    ∃ ω : ℝ, ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool) {Y : ℝ} (hY : 0 < Y),
      (∑ a : Slots D k upper, ‖rawSlot D r k upper negativeM J j ell Y a‖)^2 ≤
        (cosineCost * profileBudget ell hY)^2 *
          (((2 + Real.log (4*V+1))^2 *
            ((pascadiJ (classicalLevels (Z/2)) W j ω +
              pascadiJ (classicalLevels Z) W j ω)/4)) *
            ∑ a : Slots D k upper, (inverseWeightedRawN D r k upper negativeM j ell a)^2) := by
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
  intro r negativeM Y hY
  let G := inverseWeightedRawN D r k upper negativeM j ell
  have hsplit : (∑ a : Slots D k upper,
      ‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
      ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖) =
      ∑ a : Slots D k upper, F a * G a := by
    apply Finset.sum_congr rfl
    intro a _
    have hp : 0 < Real.sqrt (W ^ tau a.1.val a.2.val) :=
      Real.sqrt_pos.2 (Real.rpow_pos_of_pos hW _)
    dsimp only [F,G,mFactor,inverseWeightedRawN,W,V,Z]
    field_simp [hp.ne'] <;> ring
  have hs := raw_chart_le_profileBudget D r k upper negativeM J j ell hY
  have hnon : 0 ≤ ∑ a : Slots D k upper, ‖rawSlot D r k upper negativeM J j ell Y a‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq := pow_le_pow_left₀ hnon hs 2
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G
  have henergy := hcauchy.trans
    (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg (fun a _ => sq_nonneg (G a))))
  calc
    _ ≤ ((cosineCost * profileBudget ell hY) *
        ∑ a : Slots D k upper,
          ‖originalMFunctional J j ell a.1.val.val a.1.val.property a.2.val‖ *
          ‖originalNFunctional D r k upper negativeM ell a.1.val.val a.1.val.property a.2.val‖)^2 := hsq
    _ = (cosineCost * profileBudget ell hY)^2 * (∑ a : Slots D k upper, F a*G a)^2 := by rw [hsplit,mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy (sq_nonneg _)

end ImbalancedChen.Part3.OriginalPositiveProfileBudget20261120
end
