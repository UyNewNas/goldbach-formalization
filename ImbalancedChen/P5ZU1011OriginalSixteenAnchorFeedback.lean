import ImbalancedChen.P5ZU1011OriginalSixteenReassembly

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Genuine analytic K feedback for the UNCHANGED original sixteen-policy
minimum. H248, all15 selected-mask policies, the distinct W policy and all
eligibility predicates are fixed. Only the switched coefficient k varies.
The anchor switch region is defined by the actual all16 ordinary costs;
it is proved to be exactly the original least-tag-zero winner region.

The feedback slope is its actual weighted switch-base integral, constructed
here with integrability. No saved slope, hFeedback, hSlope, whole mean or
numeric retained-decrease licence is assumed. In particular this source
does NOT prove that the original savedRetainedCostDecrease is below this
slope. The numerical lower-endpoint licence remains OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenAnchorFeedback

noncomputable section
open Set MeasureTheory
open Classical
open U11Integral U11Canonical U11H248 U1011AdaptivePrimeError
open U1011OriginalSixteenPolicyBank
open scoped BigOperators

def switchBase : LogFour → ℝ := switchedKernel 1 LiLiuPrereqBuchstab.buchstab

def ordinary : ℕ → LogFour → ℝ := ordinaryKernel H248 residual

def candidates (k : ℝ) : ℕ → LogFour → ℝ :=
  guarded eligible (switchedKernel k LiLiuPrereqBuchstab.buchstab) ordinary

def cost (k : ℝ) : LogFour → ℝ := envelope bank (candidates k)

/-- Full original method-zero anchor: the switched cost is no larger
than EVERY eligible ordinary policy, including W. Ties remain at tag0. -/
def anchorSwitchRegion (k0 : ℝ) : Set LogFour :=
  {v | ∀ j ∈ bank, eligible j v → switchedKernel k0 LiLiuPrereqBuchstab.buchstab v ≤ ordinary j v}

theorem switchedKernel_eq_mul_base (k : ℝ) (v : LogFour) :
    switchedKernel k LiLiuPrereqBuchstab.buchstab v=k*switchBase v := by
  unfold switchedKernel switchBase
  ring

theorem switchBase_nonneg (mask : Set (ℝ×ℝ)) (v : LogFour)
    (hv : v ∈ originalDomain mask) : 0≤switchBase v :=
  canonical_switched_nonneg mask 1 (by norm_num) v hv

theorem measurable_ordinary (j : ℕ) : Measurable (ordinary j) :=
  measurable_ordinaryKernel H248 residual j measurable_H248 (measurable_residual j)

theorem measurable_cost (k : ℝ) : Measurable (cost k) := by
  apply measurable_envelope
  apply measurable_guarded
  · intro j _
    exact measurableSet_eligible j
  · exact measurable_switchedKernel k _ LiLiuPrereqBuchstab.continuous_buchstab.measurable
  · intro j _
    exact measurable_ordinary j

theorem measurableSet_anchorSwitchRegion (k0 : ℝ) : MeasurableSet (anchorSwitchRegion k0) := by
  have heq : anchorSwitchRegion k0 = ⋂ j : {j : ℕ // j ∈ bank},
      {v | eligible j.val v → switchedKernel k0 LiLiuPrereqBuchstab.buchstab v≤ordinary j.val v} := by
    ext v
    simp only [anchorSwitchRegion,Set.mem_setOf_eq,Set.mem_iInter]
    constructor
    · intro h j
      exact h j.val j.property
    · intro h j hj
      exact h ⟨j,hj⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  have himp : {v | eligible j.val v → switchedKernel k0 LiLiuPrereqBuchstab.buchstab v≤ordinary j.val v} =
      {v | eligible j.val v}ᶜ ∪
        {v | switchedKernel k0 LiLiuPrereqBuchstab.buchstab v≤ordinary j.val v} := by
    ext v
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff,Set.mem_union]
    tauto
  rw [himp]
  exact (measurableSet_eligible j.val).compl.union
    (measurableSet_le (measurable_switchedKernel k0 _
      LiLiuPrereqBuchstab.continuous_buchstab.measurable) (measurable_ordinary j.val))
theorem switched_mono_on_original {k k0 : ℝ} (hk : k≤k0)
    (mask : Set (ℝ×ℝ)) (v : LogFour) (hv : v ∈ originalDomain mask) :
    switchedKernel k LiLiuPrereqBuchstab.buchstab v≤
      switchedKernel k0 LiLiuPrereqBuchstab.buchstab v := by
  rw [switchedKernel_eq_mul_base,switchedKernel_eq_mul_base]
  exact mul_le_mul_of_nonneg_right hk (switchBase_nonneg mask v hv)

/-- Actual16 monotonicity uses the same all16 candidates pointwise.
Ineligible tags retain the switched fallback on BOTH sides. -/
theorem cost_mono_on_original {k k0 : ℝ} (hk : k≤k0)
    (mask : Set (ℝ×ℝ)) (v : LogFour) (hv : v ∈ originalDomain mask) : cost k v≤cost k0 v := by
  have hs := switched_mono_on_original hk mask v hv
  have h := envelope_le_add bank (candidates k) (candidates k0) v 0 (fun c hc => by
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simpa only [candidates,guarded,if_pos rfl,add_zero] using hs
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hc
      by_cases he : eligible j v
      · simp [candidates,guarded,he]
      · simpa [candidates,guarded,he] using hs)
  simpa only [cost,add_zero] using h

/-- The anchor switched winner remains switched when k is lowered.
This proves the true cost identity, with no pre-assumed cell bound. -/
theorem cost_eq_switched_on_anchor {k k0 : ℝ} (hk : k≤k0)
    (mask : Set (ℝ×ℝ)) (v : LogFour) (hv : v ∈ originalDomain mask)
    (ha : v ∈ anchorSwitchRegion k0) :
    cost k v=switchedKernel k LiLiuPrereqBuchstab.buchstab v := by
  have hs := switched_mono_on_original hk mask v hv
  apply le_antisymm
  · exact guarded_envelope_le_switched bank eligible _ ordinary v
  · rw [cost,envelope_eq_min]
    apply Finset.le_min'
    intro y hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simp only [candidates,guarded,if_pos rfl,le_refl]
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hc
      by_cases he : eligible j v
      · simpa [candidates,guarded,he] using hs.trans (ha j hj he)
      · simp only [candidates,guarded,Nat.succ_ne_zero,if_false,Nat.pred_succ,if_neg he,le_refl]

/-- The literal anchor region equals the actual least-tag-zero winner
on the original support. It is not an arbitrary selected slope cell. -/
theorem anchor_iff_winner_zero (k0 : ℝ) (mask : Set (ℝ×ℝ))
    (v : LogFour) (hv : v ∈ originalDomain mask) :
    v ∈ anchorSwitchRegion k0 ↔ v ∈ winner (originalDomain mask) bank (candidates k0) 0 := by
  constructor
  · intro ha
    refine ⟨hv,?_,?_⟩
    · simpa only [candidates,guarded,if_pos rfl,cost] using
        (cost_eq_switched_on_anchor le_rfl mask v hv ha).symm
    · intro d _ hd
      omega
  · intro hw j hj he
    have hcost := envelope_le bank (candidates k0) v j.succ
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,hj,rfl⟩))
    have hzero : switchedKernel k0 LiLiuPrereqBuchstab.buchstab v=cost k0 v := by
      simpa only [candidates,guarded,if_pos rfl,cost] using hw.2.1
    rw [←hzero] at hcost
    simpa [candidates,guarded,he] using hcost

/-- Exact linear change on the ACTUAL unchanged method-zero region. -/
theorem cost_exact_decrease_on_anchor {k k0 : ℝ} (hk : k≤k0)
    (mask : Set (ℝ×ℝ)) (v : LogFour) (hv : v ∈ originalDomain mask)
    (ha : v ∈ anchorSwitchRegion k0) :
    cost k v=cost k0 v-(k0-k)*switchBase v := by
  rw [cost_eq_switched_on_anchor hk mask v hv ha,
    cost_eq_switched_on_anchor le_rfl mask v hv ha,
    switchedKernel_eq_mul_base,switchedKernel_eq_mul_base]
  ring

/-- Outside the anchor region only monotonicity is charged. Thus the
actual decrease is at least its explicit method-zero contribution. -/
theorem cost_le_anchor_minus_indicator {k k0 : ℝ} (hk : k≤k0)
    (mask : Set (ℝ×ℝ)) (v : LogFour) (hv : v ∈ originalDomain mask) :
    cost k v≤cost k0 v-(k0-k)*(anchorSwitchRegion k0).indicator switchBase v := by
  by_cases ha : v ∈ anchorSwitchRegion k0
  · rw [indicator_of_mem ha,cost_exact_decrease_on_anchor hk mask v hv ha]
  · rw [indicator_of_notMem ha,mul_zero,sub_zero]
    exact cost_mono_on_original hk mask v hv

/-- Fixed original H248/all16 bounds provide every K-family envelope
integrability prerequisite. No analytic slope or mean is supplied. -/
theorem cost_bounds_on_original (k : ℝ) (hk : 0≤k) (mask : Set (ℝ×ℝ))
    (v : LogFour) (hv : v ∈ originalDomain mask) :
    0≤cost k v ∧ cost k v≤switchedKernel k LiLiuPrereqBuchstab.buchstab v := by
  apply guarded_envelope_bounds (originalDomain mask) bank eligible _ ordinary
  · exact canonical_switched_nonneg mask k hk
  · intro j _ v hv he
    exact (ordinary_actual_bounds mask j v hv he).1
  · exact hv

theorem integrableOn_weighted_cost (k : ℝ) (hk : 0≤k) (mask : Set (ℝ×ℝ))
    (hm : MeasurableSet mask) :
    IntegrableOn (fun v => cost k v*harmonicDensity v) (originalDomain mask) volume := by
  have hmeas : Measurable (fun v => cost k v*harmonicDensity v) := by
    apply (measurable_cost k).mul
    unfold harmonicDensity
    fun_prop
  apply (integrableOn_original_weighted_switched mask k).mono_nonneg hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain mask hm)] with v hv
    exact mul_nonneg (cost_bounds_on_original k hk mask v hv).1
      (U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original mask v hv)
  · filter_upwards [ae_restrict_mem (measurableSet_originalDomain mask hm)] with v hv
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (cost_bounds_on_original k hk mask v hv).2
      (U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original mask v hv)

def slopeIntegrand (k0 : ℝ) (v : LogFour) : ℝ :=
  (anchorSwitchRegion k0).indicator switchBase v*harmonicDensity v

theorem integrableOn_slopeIntegrand (k0 : ℝ) (mask : Set (ℝ×ℝ)) :
    IntegrableOn (slopeIntegrand k0) (originalDomain mask) volume := by
  have heq : slopeIntegrand k0=(anchorSwitchRegion k0).indicator
      (fun v => switchBase v*harmonicDensity v) := by
    funext v
    by_cases ha : v ∈ anchorSwitchRegion k0 <;> simp [slopeIntegrand,ha]
  rw [heq]
  have hi : IntegrableOn (fun v => switchBase v*harmonicDensity v) (originalDomain mask) volume := by
    simpa only [switchBase,mul_comm] using integrableOn_original_weighted_switched mask 1
  exact hi.indicator (measurableSet_anchorSwitchRegion k0)

def costIntegral (k : ℝ) (mask : Set (ℝ×ℝ)) : ℝ :=
  ∫ v in originalDomain mask, cost k v*harmonicDensity v

def anchorSlope (k0 : ℝ) (mask : Set (ℝ×ℝ)) : ℝ :=
  ∫ v in originalDomain mask, slopeIntegrand k0 v

theorem anchorSlope_nonneg (k0 : ℝ) (mask : Set (ℝ×ℝ)) (hm : MeasurableSet mask) :
    0≤anchorSlope k0 mask := by
  apply setIntegral_nonneg (measurableSet_originalDomain mask hm)
  intro v hv
  apply mul_nonneg
  · by_cases ha : v ∈ anchorSwitchRegion k0
    · rw [indicator_of_mem ha]
      exact switchBase_nonneg mask v hv
    · simpa only [indicator_of_notMem ha] using (le_rfl : (0 : ℝ)≤0)
  · exact U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original mask v hv

/-- Exact identification of the constructed slope with the actual
method-zero winner integral, retaining the original least-tag convention. -/
theorem anchorSlope_eq_winner_zero_integral (k0 : ℝ) (mask : Set (ℝ×ℝ)) :
    anchorSlope k0 mask = ∫ v in winner (originalDomain mask) bank (candidates k0) 0,
      switchBase v*harmonicDensity v := by
  have heq : slopeIntegrand k0=(anchorSwitchRegion k0).indicator
      (fun v => switchBase v*harmonicDensity v) := by
    funext v
    by_cases ha : v ∈ anchorSwitchRegion k0 <;> simp [slopeIntegrand,ha]
  have hset : originalDomain mask ∩ anchorSwitchRegion k0 =
      winner (originalDomain mask) bank (candidates k0) 0 := by
    ext v
    constructor
    · intro hv
      exact (anchor_iff_winner_zero k0 mask v hv.1).1 hv.2
    · intro hw
      exact ⟨hw.1,(anchor_iff_winner_zero k0 mask v hw.1).2 hw⟩
  rw [anchorSlope,heq,setIntegral_indicator (measurableSet_anchorSwitchRegion k0),hset]
/-- Genuine original16 feedback inequality. The slope is the integral
CONSTRUCTED above, rather than the original saved numerical slope assumed
as a hypothesis. Mask geometry is fixed and only its measurability is used. -/
theorem costIntegral_le_anchor_sub_slope {k k0 : ℝ} (hk : 0≤k) (hkk0 : k≤k0)
    (mask : Set (ℝ×ℝ)) (hm : MeasurableSet mask) :
    costIntegral k mask≤costIntegral k0 mask-(k0-k)*anchorSlope k0 mask := by
  have hk0 : 0≤k0 := hk.trans hkk0
  have hleft := integrableOn_weighted_cost k hk mask hm
  have hright := (integrableOn_weighted_cost k0 hk0 mask hm).sub
    ((integrableOn_slopeIntegrand k0 mask).const_mul (k0-k))
  have hcomp := setIntegral_mono_on hleft hright (measurableSet_originalDomain mask hm)
    (fun v hv => by
      have h := mul_le_mul_of_nonneg_right
        (cost_le_anchor_minus_indicator hkk0 mask v hv)
        (U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original mask v hv)
      convert h using 1 <;> dsimp [slopeIntegrand] <;> ring)
  simpa only [costIntegral,anchorSlope,integral_sub
    (integrableOn_weighted_cost k0 hk0 mask hm)
    ((integrableOn_slopeIntegrand k0 mask).const_mul (k0-k)),integral_const_mul] using hcomp

/-- The current-k member is definitionally the SAME actual original
sixteen-policy envelope whose independent harmonic mean was proved. -/
theorem cost_currentK : cost currentK=U1011OriginalSixteenReassembly.actualMinimum := rfl

end
end ImbalancedChen.P5Z.U1011OriginalSixteenAnchorFeedback


