import ImbalancedChen.P5ZU1011OriginalSixteenAnchorFeedback
import ImbalancedChen.P5ZU1011OriginalJointHarmonic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Genuine JOINT original16 K feedback: U10 low-fourth is wholly unmasked;
U11 high-fourth keeps the original fixed mask. The former anchor module
concerned U11 ONLY. Here the actual D10 Buchstab range supplies switch-base
positivity, and the true full-square gates supply ordinary positivity.
Both weighted K-family integrals and both actual method-zero slopes are
constructed. No saved numerical slope, hSlope, hFeedback or mean is assumed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenJointAnchorFeedback

noncomputable section
open Set MeasureTheory
open Classical
open scoped BigOperators
open U11Integral U11Canonical U11H248
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenAnchorFeedback
open U1011OriginalSixteenU10Geometry

/-- The base sign is licensed on TRUE D10, not by U11 x>=h. -/
theorem switchBase_nonneg_D10 {v : LogFour} (hv : v ∈ domain10) : 0≤switchBase v := by
  have hs := domain10_argument_bounds hv
  have hz : 0<v 2 := (domain10_smallest_pos hv).trans hv.2.1
  have hω := LiLiuPrereqBuchstab.buchstab_nonneg
    (show (1 : ℝ)≤(1-(v 0+v 1+v 2+v 3))/v 2 by linarith [hs.1])
  simpa only [switchBase,switchedKernel,one_mul] using div_nonneg hω hz.le

theorem harmonicDensity_nonneg_D10 {v : LogFour} (hv : v ∈ domain10) : 0≤harmonicDensity v := by
  have hc := domain10_subset_compactBox hv
  have hp (i : Fin 4) : 0<v i := by linarith [hc.1 i]
  exact div_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (mul_nonneg (hp 0).le (hp 1).le) (hp 2).le) (hp 3).le)

/-- Original H248 and TRUE eligible residual>w prove ordinary positivity
on the low band independently of every high-band domain premise. -/
theorem ordinary_nonneg_D10 {v : LogFour} (hv : v ∈ domain10)
    (j : ℕ) (he : eligible j v) : 0≤ordinary j v := by
  have hj : j<16 := by
    by_contra hn
    simp only [eligible,dif_neg hn] at he
  let p : Policy:=⟨j,hj⟩
  have heP : TypedEligible p v := by simpa only [eligible,dif_pos hj] using he
  have hR : 0<typedResidual p v :=
    (domain10_smallest_pos hv).trans (typedEligible_residual_gt_smallest p v heP)
  have hH := H248_max_two_bounds (typedResidual p v/v 3)
  have hres : residual j v=typedResidual p v := by simp only [residual,dif_pos hj,p]
  rw [ordinary,ordinaryKernel,hres]
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hH.2)) hR.le

theorem switched_mono_D10 {k k0 : ℝ} (hk : k≤k0) {v : LogFour} (hv : v ∈ domain10) :
    switchedKernel k LiLiuPrereqBuchstab.buchstab v≤switchedKernel k0 LiLiuPrereqBuchstab.buchstab v := by
  rw [switchedKernel_eq_mul_base,switchedKernel_eq_mul_base]
  exact mul_le_mul_of_nonneg_right hk (switchBase_nonneg_D10 hv)

theorem cost_mono_D10 {k k0 : ℝ} (hk : k≤k0) {v : LogFour} (hv : v ∈ domain10) : cost k v≤cost k0 v := by
  have hs:=switched_mono_D10 hk hv
  have h:=U1011AdaptivePrimeError.envelope_le_add bank (candidates k) (candidates k0) v 0 (fun c hc => by
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simpa only [candidates,guarded,if_pos rfl,add_zero] using hs
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hc
      by_cases he : eligible j v
      · simp [candidates,guarded,he]
      · simpa [candidates,guarded,he] using hs)
  simpa only [cost,add_zero] using h

theorem cost_eq_switched_on_D10_anchor {k k0 : ℝ} (hk : k≤k0) {v : LogFour}
    (hv : v ∈ domain10) (ha : v ∈ anchorSwitchRegion k0) :
    cost k v=switchedKernel k LiLiuPrereqBuchstab.buchstab v := by
  have hs:=switched_mono_D10 hk hv
  apply le_antisymm
  · exact guarded_envelope_le_switched bank eligible _ ordinary v
  · rw [cost,envelope_eq_min]
    apply Finset.le_min'
    intro y hy
    obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hy
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simp only [candidates,guarded,if_pos rfl,le_refl]
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hc
      by_cases he : eligible j v
      · simpa [candidates,guarded,he] using hs.trans (ha j hj he)
      · simp only [candidates,guarded,Nat.succ_ne_zero,if_false,Nat.pred_succ,if_neg he,le_refl]

theorem cost_le_anchor_minus_indicator_D10 {k k0 : ℝ} (hk : k≤k0) {v : LogFour}
    (hv : v ∈ domain10) : cost k v≤cost k0 v-(k0-k)*(anchorSwitchRegion k0).indicator switchBase v := by
  by_cases ha : v ∈ anchorSwitchRegion k0
  · rw [indicator_of_mem ha,cost_eq_switched_on_D10_anchor hk hv ha,
      cost_eq_switched_on_D10_anchor le_rfl hv ha,switchedKernel_eq_mul_base,switchedKernel_eq_mul_base]
    apply le_of_eq
    ring
  · rw [indicator_of_notMem ha,mul_zero,sub_zero]
    exact cost_mono_D10 hk hv

theorem cost_bounds_D10 (k : ℝ) (hk : 0≤k) {v : LogFour} (hv : v ∈ domain10) :
    0≤cost k v ∧ cost k v≤switchedKernel k LiLiuPrereqBuchstab.buchstab v := by
  apply guarded_envelope_bounds domain10 bank eligible _ ordinary
  · intro v hv
    rw [switchedKernel_eq_mul_base]
    exact mul_nonneg hk (switchBase_nonneg_D10 hv)
  · intro j _ v hv he
    exact ordinary_nonneg_D10 hv j he
  · exact hv

theorem integrableOn_weighted_switch_D10 (k : ℝ) :
    IntegrableOn (fun v => harmonicDensity v*switchedKernel k LiLiuPrereqBuchstab.buchstab v) domain10 :=
  ((continuousOn_harmonicDensity_compactBox.mul (continuousOn_canonical_switched_compactBox k)).integrableOn_compact
    isCompact_compactBox).mono_set domain10_subset_compactBox

theorem integrableOn_weighted_cost_D10 (k : ℝ) (hk : 0≤k) :
    IntegrableOn (fun v => cost k v*harmonicDensity v) domain10 := by
  have hmeas : Measurable (fun v => cost k v*harmonicDensity v) := by
    apply (measurable_cost k).mul
    unfold harmonicDensity
    fun_prop
  apply (integrableOn_weighted_switch_D10 k).mono_nonneg hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_domain10] with v hv
    exact mul_nonneg (cost_bounds_D10 k hk hv).1 (harmonicDensity_nonneg_D10 hv)
  · filter_upwards [ae_restrict_mem measurableSet_domain10] with v hv
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (cost_bounds_D10 k hk hv).2
      (harmonicDensity_nonneg_D10 hv)

theorem integrableOn_slopeIntegrand_D10 (k0 : ℝ) : IntegrableOn (slopeIntegrand k0) domain10 := by
  have heq : slopeIntegrand k0=(anchorSwitchRegion k0).indicator
      (fun v => switchBase v*harmonicDensity v) := by
    funext v
    by_cases ha : v ∈ anchorSwitchRegion k0 <;> simp [slopeIntegrand,ha]
  rw [heq]
  have hi : IntegrableOn (fun v => switchBase v*harmonicDensity v) domain10 := by
    simpa only [switchBase,mul_comm] using integrableOn_weighted_switch_D10 1
  exact hi.indicator (measurableSet_anchorSwitchRegion k0)

theorem slopeIntegrand_nonneg_D10 (k0 : ℝ) {v : LogFour} (hv : v ∈ domain10) : 0≤slopeIntegrand k0 v := by
  apply mul_nonneg
  · by_cases ha : v ∈ anchorSwitchRegion k0
    · rw [indicator_of_mem ha]
      exact switchBase_nonneg_D10 hv
    · simp only [indicator_of_notMem ha,le_refl]
  · exact harmonicDensity_nonneg_D10 hv

def costIntegral10 (k : ℝ) : ℝ:=∫ v in domain10,cost k v*harmonicDensity v
def anchorSlope10 (k0 : ℝ) : ℝ:=∫ v in domain10,slopeIntegrand k0 v

theorem feedback_D10 {k k0 : ℝ} (hk : 0≤k) (hkk0 : k≤k0) :
    costIntegral10 k≤costIntegral10 k0-(k0-k)*anchorSlope10 k0 := by
  have hk0:=hk.trans hkk0
  have hright:=(integrableOn_weighted_cost_D10 k0 hk0).sub
    ((integrableOn_slopeIntegrand_D10 k0).const_mul (k0-k))
  have h:=setIntegral_mono_on (integrableOn_weighted_cost_D10 k hk) hright measurableSet_domain10 (fun v hv => by
    have hh:=mul_le_mul_of_nonneg_right (cost_le_anchor_minus_indicator_D10 hkk0 hv)
      (harmonicDensity_nonneg_D10 hv)
    convert hh using 1 <;> dsimp [slopeIntegrand] <;> ring)
  simpa only [costIntegral10,anchorSlope10,integral_sub (integrableOn_weighted_cost_D10 k0 hk0)
    ((integrableOn_slopeIntegrand_D10 k0).const_mul (k0-k)),integral_const_mul] using h

/-- The true JOINT functional has low band UNMASKED and high band with
exactly the original fixed mask. The former D11-only functional is not renamed joint. -/
def jointCostIntegral (k : ℝ) (mask : Set (ℝ×ℝ)) : ℝ:=costIntegral10 k+costIntegral k mask
def jointAnchorSlope (k0 : ℝ) (mask : Set (ℝ×ℝ)) : ℝ:=anchorSlope10 k0+anchorSlope k0 mask

theorem jointCostIntegral_eq_union (k : ℝ) (hk : 0≤k) (mask : Set (ℝ×ℝ)) (hm : MeasurableSet mask) :
    jointCostIntegral k mask=∫ v in domain10 ∪ originalDomain mask,cost k v*harmonicDensity v := by
  exact (setIntegral_union (U1011OriginalJointHarmonic.domain10_disjoint_originalDomain mask)
    (measurableSet_originalDomain mask hm) (integrableOn_weighted_cost_D10 k hk)
    (integrableOn_weighted_cost k hk mask hm)).symm

/-- TRUE both-band feedback with a constructed real SJ. No saved slope,
hFeedback, hSlope or harmonic mean is supplied by a caller. -/
theorem joint_feedback {k k0 : ℝ} (hk : 0≤k) (hkk0 : k≤k0)
    (mask : Set (ℝ×ℝ)) (hm : MeasurableSet mask) :
    jointCostIntegral k mask≤jointCostIntegral k0 mask-(k0-k)*jointAnchorSlope k0 mask := by
  have h:=add_le_add (feedback_D10 hk hkk0) (costIntegral_le_anchor_sub_slope hk hkk0 mask hm)
  convert h using 1 <;> dsimp [jointCostIntegral,jointAnchorSlope] <;> ring

/-- At currentK this is exactly the independently proved TRUE native
joint harmonic integral, with original same-row mask and no extra factor1/4. -/
theorem jointCost_currentK (S : Finset Certificates.PairedV2.FullMask.Row) :
    jointCostIntegral currentK (U1011OriginalPairedFixedMaskHarmonic.outerUnion S)=
      U1011OriginalJointHarmonic.jointIntegral S := by
  rw [U1011OriginalJointHarmonic.jointIntegral_eq_band_sum]
  rfl

end
end ImbalancedChen.P5Z.U1011OriginalSixteenJointAnchorFeedback

