import ImbalancedChen.P2N96PriorityRawOmegaQuery
import ImbalancedChen.P2N48PriorityActualCostExpansion
import ImbalancedChen.P2N48WholeHighLiteralFunctional

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual child Omega queries pay the SAME retained child integrals.
The priority upper uses anchorK, as in the original subdivision source;
it does not book the separate nonpriority current-K slope on priority rows.
True child masses remain integrals, not fabricated child Q80 endpoints.
-/
namespace ImbalancedChen.P2N96PrioritySameMaskCost
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48TiedParentMassReduction
open P2N48PriorityHalfGridDictionary P2N48PriorityActualCostExpansion
open P2N48WholeHighLiteralFunctional P2N96PriorityRawOmegaQuery
open OriginalN48Q112LocalProduct P2N48OriginalQ80DirectedRowSoundness
open P5Z.U11Integral P5Z.U11Canonical P5Z.U1011OriginalSixteenAnchorFeedback

def childWeightedMass (r : SourceRow) (b : HalfBits) : ℝ :=
  parentUnweightedMass (childSelectedParent r b)

/-- The unchanged original K0 is used for the priority replacement. -/
def childOmegaUpper (r : SourceRow) (b : HalfBits) : ℝ :=
  anchorK*uniformOmegaUpper (childOriginalQueryToken r b)*childWeightedMass r b

def completeChildOmegaUpper (r : SourceRow) : ℝ :=
  ∑ b∈originalHighChildren r,childOmegaUpper r b

theorem child_selected_subset_full (r : SourceRow) (b : HalfBits) :
    childSelectedParent r b⊆fullParent r :=
  (childSelectedParent_subset_parent r b).trans (selectedParent_subset_fullParent r actualMask)

/-- Genuine quantitative payment: the nonlinear original-sixteen cost is
bounded by a separately proved raw Omega query on each real n96 child.
There is no child-cost inequality or real mass enclosure among the inputs. -/
theorem child_actual_cost_le_omega_proposal (r : SourceRow) (ht : r.term.val=1)
    (b : HalfBits) : childActualCost r b≤childOmegaUpper r b := by
  have hi := integrable_actualKernel.mono_set
    ((childSelectedParent_subset_parent r b).trans (selectedParent_subset_actualDomain r))
  have hmass := (integrable_unweightedDensity_fullParent r).mono_set
    (child_selected_subset_full r b)
  have hpoint : ∀ v∈childSelectedParent r b,
      actualKernel v≤(anchorK*uniformOmegaUpper (childOriginalQueryToken r b))*
        (harmonicDensity v/v 2) := by
    intro v hv
    have hD : v∈originalDomain actualMask := by
      simpa [childSelectedParent,ht] using hv.2
    have hF := child_selected_subset_full r b hv
    have hz := row_coordinate_pos r v hF 2
    have hd := P5Z.U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original
      actualMask v hD
    have hk : ImbalancedChen.currentK≤anchorK := by
      norm_num [ImbalancedChen.currentK,anchorK]
    have hc := (cost_bounds_on_original ImbalancedChen.currentK
      (by norm_num [ImbalancedChen.currentK]) actualMask v hD).2
    have hmono := switched_mono_on_original hk actualMask v hD
    have hswitch : cost ImbalancedChen.currentK v*harmonicDensity v≤
        switchedKernel anchorK LiLiuPrereqBuchstab.buchstab v*harmonicDensity v :=
      mul_le_mul_of_nonneg_right (hc.trans hmono) hd
    have hq := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (child_query_upper_proposal r b hv.1)
        (div_nonneg hd hz.le)) (show (0 : ℝ)≤anchorK by norm_num [anchorK])
    have hupper : switchedKernel anchorK LiLiuPrereqBuchstab.buchstab v*harmonicDensity v≤
        (anchorK*uniformOmegaUpper (childOriginalQueryToken r b))*(harmonicDensity v/v 2) := by
      convert hq using 1 <;> simp only [switchedKernel,omegaArgument] <;> ring
    change cost ImbalancedChen.currentK v*harmonicDensity v≤_
    exact hswitch.trans hupper
  have h := setIntegral_mono_on hi
    (hmass.const_mul (anchorK*uniformOmegaUpper (childOriginalQueryToken r b)))
    (measurableSet_childSelectedParent r b) hpoint
  simpa only [childActualCost,childOmegaUpper,childWeightedMass,parentUnweightedMass,
    integral_const_mul] using h

theorem parent_actual_cost_le_complete_child_omega_proposal
    (r : SourceRow) (ht : r.term.val=1) :
    parentCost ImbalancedChen.currentK (selectedParent r actualMask)≤completeChildOmegaUpper r := by
  rw [original_high_parent_actual_cost r ht]
  exact Finset.sum_le_sum (fun b _ => child_actual_cost_le_omega_proposal r ht b)

def keyAnchorBaseline (k : P2N48CompleteHighPhysicalCover.HighKey) : ℝ :=
  anchorK*omegaCap*parentUnweightedMass (fullParent (keyActualRow k))

def keyOldSaving (k : P2N48CompleteHighPhysicalCover.HighKey) : ℝ :=
  ((keyActualRow k).floorQ : ℝ)/floorScale

def keyChildSaving (k : P2N48CompleteHighPhysicalCover.HighKey) : ℝ :=
  keyAnchorBaseline k-completeChildOmegaUpper (keyActualRow k)

/-- The method0 parent licence and all children compete for ONE cost.
Other old methods have no new historical floor licence here. -/
def keyPriorityUpper (k : P2N48CompleteHighPhysicalCover.HighKey) : ℝ :=
  if (keyActualRow k).method=0 then
    min (savedParent (keyActualRow k) (parentUnweightedMass (fullParent (keyActualRow k))))
      (completeChildOmegaUpper (keyActualRow k))
  else completeChildOmegaUpper (keyActualRow k)

theorem key_priority_upper_sound_proposal (k : P2N48CompleteHighPhysicalCover.HighKey)
    (hk : k∈P2N48CompleteHighPhysicalCover.highKeys) : keyActualCost k≤keyPriorityUpper k := by
  have hc := parent_actual_cost_le_complete_child_omega_proposal
    (keyActualRow k) (actual_key_is_high_proposal k hk)
  change keyActualCost k≤completeChildOmegaUpper (keyActualRow k) at hc
  by_cases hm : (keyActualRow k).method=0
  · rw [keyPriorityUpper,if_pos hm]
    apply le_min _ hc
    have h := actual_key_method_zero_current_cost_proposal k hk hm
    exact h.trans (sub_le_self _ (show 0≤rowGainLower (keyActualRow k) from le_max_left _ _))
  · simpa only [keyPriorityUpper,if_neg hm] using hc

private theorem min_cost_eq_max_saving (B s C : ℝ) :
    min (B-s) C=B-max s (B-C) := by
  by_cases h : B-s≤C
  · rw [min_eq_left h,max_eq_left (by linarith : B-C≤s)]
  · rw [min_eq_right (le_of_not_ge h),max_eq_right (by linarith : s≤B-C)]
    ring

/-- The old Q80 saving is not ADDED to the child saving. Both use the
same independently defined full-parent anchor baseline, while the child
mass itself retains the actual deletion mask. No historical child floor
or claimed numerical priority gain is identified with keyChildSaving. -/
theorem priority_method_zero_exact_maximum (k : P2N48CompleteHighPhysicalCover.HighKey)
    (hm : (keyActualRow k).method=0) :
    keyPriorityUpper k=keyAnchorBaseline k-max (keyOldSaving k) (keyChildSaving k) := by
  rw [keyPriorityUpper,if_pos hm]
  exact min_cost_eq_max_saving _ _ _

end
end ImbalancedChen.P2N96PrioritySameMaskCost
