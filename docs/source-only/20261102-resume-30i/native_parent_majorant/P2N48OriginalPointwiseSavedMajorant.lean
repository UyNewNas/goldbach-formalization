import ImbalancedChen.OriginalPairedN48RequiredRowQ112Bridge

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original method0 producer uses a UNIFORM omega query times the SAME
ordered reference mass Z. This stronger fact, not its integrated corollary,
licenses division by Z. The original max(0,...) Q112/Q80 comparison is kept.
All inherited closed producer/log/floor decisions remain unevaluated.
-/
namespace ImbalancedChen.P2N48OriginalPointwiseSavedMajorant
noncomputable section
open Set MeasureTheory
open LiLiuPrereqBuchstab
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48MethodZeroQ112SwitchReduction P2N48TiedParentMassReduction
open P2N48OriginalQ80DirectedRowSoundness P2N48SelectedFunctionalRemainder
open OriginalN48Q112LocalProduct OriginalPairedN48AllNativeQueryGeometry
open OriginalPairedN48Q112ClampedReceiver OriginalPairedN48RequiredRowQ112Bridge
open P5Z.U11Integral P5Z.U11Canonical
open P5Z.U1011OriginalSixteenAnchorFeedback
open scoped BigOperators

/-- The same original constant-times-Z endpoint supplies the pointwise
numerator. An upper bound for the integrated switched mass would not do. -/
theorem original_max_floor_pointwise_numerator (r : SourceRow)
    (e : DirectedMethodZeroRow) (omegaUpper : ℝ)
    (hLo : (e.switchBaselineLo : ℝ) / (replayP : ℝ) ≤
      anchorK * omegaCap * parentUnweightedMass (fullParent r))
    (hHi : anchorK * omegaUpper * parentUnweightedMass (fullParent r) ≤
      (e.omegaCostHi : ℝ) / (replayP : ℝ))
    (hOmega : ∀ v ∈ fullParent r, buchstab (omegaArgument v) ≤ omegaUpper)
    (hcheck : originalRowMaxFloorCheck r e = true)
    {v : LogFour} (hv : v ∈ fullParent r) :
    anchorK * buchstab (omegaArgument v) * parentUnweightedMass (fullParent r) ≤
      savedParent r (parentUnweightedMass (fullParent r)) := by
  have hk : 0 ≤ anchorK := by norm_num [anchorK]
  have hZ := true_parent_mass_nonneg r
  have hT : anchorK * buchstab (omegaArgument v) * parentUnweightedMass (fullParent r) ≤
      (e.omegaCostHi : ℝ) / (replayP : ℝ) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hOmega v hv) hk) hZ).trans hHi
  have hCap := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (actual_parent_buchstab_cap r hv) hk) hZ
  have hF := of_decide_eq_true (show decide ((r.floorQ : ℤ) * replayP ≤
      max 0 (e.switchBaselineLo - e.omegaCostHi) * replayQ) = true from hcheck)
  by_cases hd : 0 ≤ e.switchBaselineLo - e.omegaCostHi
  · rw [max_eq_right hd] at hF
    have hFR : (r.floorQ : ℝ) * (replayP : ℝ) ≤
        ((e.switchBaselineLo - e.omegaCostHi : ℤ) : ℝ) * (replayQ : ℝ) := by
      exact_mod_cast hF
    have hP : (0 : ℝ) < replayP := by norm_num [replayP]
    have hQ : (0 : ℝ) < replayQ := by norm_num [replayQ]
    have hUnit := (div_le_div_iff₀ hQ hP).2 hFR
    have hScale : (replayQ : ℝ) = floorScale := by norm_num [replayQ, floorScale]
    have hFloor : (r.floorQ : ℝ) / floorScale ≤
        (e.switchBaselineLo : ℝ) / (replayP : ℝ) -
          (e.omegaCostHi : ℝ) / (replayP : ℝ) := by
      simpa only [hScale, Int.cast_sub, sub_div] using hUnit
    dsimp [savedParent]
    linarith only [hLo, hT, hFloor]
  · rw [max_eq_left (le_of_not_ge hd), zero_mul] at hF
    have hP : (0 : ℤ) < replayP := by norm_num [replayP]
    have hZero : r.floorQ = 0 := by
      have hNonpos : (r.floorQ : ℤ) ≤ 0 :=
        (mul_le_mul_right hP).mp (by simpa only [zero_mul] using hF)
      omega
    simpa only [savedParent, hZero, Nat.cast_zero, zero_div, sub_zero] using hCap

/-- No real majorant, mass enclosure or supplied old-cost bound is assumed.
The original source expressions and the inherited literal floor proposal
are used before any integration occurs. -/
theorem retained_pointwise_numerator_proposal (r : SourceRow)
    (hr : r ∈ actualRetainedRows) {v : LogFour} (hv : v ∈ fullParent r) :
    anchorK * buchstab (omegaArgument v) * parentUnweightedMass (fullParent r) ≤
      savedParent r (parentUnweightedMass (fullParent r)) := by
  have hd := actual_required_same_parent_directions r hr
  exact original_max_floor_pointwise_numerator r (originalRowEndpoint r)
    (uniformOmegaUpper (rowOriginalQueryToken r)) hd.1 hd.2
    (fun v hv => all_physical_parent_query_upper_proposal r hv)
    (all_required_original_floor_check_sound all_required_original_floor_proposal r hr) hv

theorem massLower_pos (r : SourceRow) : 0 < massLower r := by
  have hw (j : Fin 4) : 0 < width r j := by
    unfold width
    split_ifs <;> norm_num
  have hn : 0 < massNumerator r := by
    unfold massNumerator
    exact Nat.mul_pos (by norm_num) (Finset.prod_pos (fun j _ => hw j))
  have hd : 0 < massDenominator r := by
    unfold massDenominator
    exact Nat.mul_pos
      (Nat.mul_pos (tieFactor_pos r) (Finset.prod_pos (fun j _ => rightEnd_pos r j)))
      (rightEnd_pos r 2)
  exact div_pos (by exact_mod_cast hn) (by exact_mod_cast hd)

theorem retained_reference_mass_pos (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    0 < parentUnweightedMass (fullParent r) :=
  (massLower_pos r).trans_le (actual_retained_massLower_sound r hr)

private theorem retained_switch_mass_nonneg (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    0 ≤ parentSwitchedMass (fullParent r) := by
  apply setIntegral_nonneg (measurableSet_fullParent r)
  intro v hv
  have ht := (P2N48ActualGeometricKeyDecoder.decoded_of_mem_rawSelectedRows r
    (actualRetainedRows_policy r hr).1).1
  have hD : v ∈ originalDomain ∅ := by
    simpa only [fullParent, if_neg (by omega : ¬r.term.val = 0)] using hv.2
  exact mul_nonneg (switchBase_nonneg ∅ v hD)
    (P5Z.U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hD)

theorem retained_saved_nonneg (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    0 ≤ savedParent r (parentUnweightedMass (fullParent r)) :=
  (mul_nonneg (by norm_num [anchorK]) (retained_switch_mass_nonneg r hr)).trans
    (actual_required_all_row_old_cost_proposal r hr)

/-- The already used exact current-K recost, retaining its positive part.
This is not a new or independently selected feedback policy. -/
def currentSavedParent (r : SourceRow) : ℝ :=
  savedParent r (parentUnweightedMass (fullParent r)) - rowGainLower r

theorem retained_feedback_lower (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    (ImbalancedChen.currentK / anchorK) * savedParent r (parentUnweightedMass (fullParent r)) ≤
      currentSavedParent r := by
  let A := savedParent r (parentUnweightedMass (fullParent r))
  have hA : 0 ≤ A := retained_saved_nonneg r hr
  have hOld : anchorK * (A / anchorK) ≤ A := by
    norm_num [anchorK] <;> ring_nf
  have h := rowGainLower_le_actual_saved_decrease r _ (A / anchorK)
    (actual_retained_massLower_sound r hr) (div_nonneg hA (by norm_num [anchorK])) hOld
  dsimp [currentSavedParent, A] at *
  norm_num [anchorK, ImbalancedChen.currentK, P2N48SavedParentRowRecost.currentK] at *
  linarith only [h]

def currentDensity (r : SourceRow) (v : LogFour) : ℝ :=
  currentSavedParent r / parentUnweightedMass (fullParent r) / v 2

/-- Actual manuscript pointwise licence, on the WHOLE original parent.
The finite floor/source dependencies remain unexecuted proof proposals. -/
theorem retained_current_pointwise_majorant_proposal (r : SourceRow)
    (hr : r ∈ actualRetainedRows) {v : LogFour} (hv : v ∈ fullParent r) :
    switchedKernel ImbalancedChen.currentK buchstab v ≤ currentDensity r v := by
  have hOld := retained_pointwise_numerator_proposal r hr hv
  have hFeedback := retained_feedback_lower r hr
  have hNum : ImbalancedChen.currentK * buchstab (omegaArgument v) *
      parentUnweightedMass (fullParent r) ≤ currentSavedParent r := by
    norm_num [anchorK, ImbalancedChen.currentK] at hOld hFeedback ⊢
    linarith only [hOld, hFeedback]
  have hCoeff := (le_div_iff₀ (retained_reference_mass_pos r hr)).2 hNum
  exact div_le_div_of_nonneg_right hCoeff (row_coordinate_pos r v hv 2).le

def weightedMajorant (r : SourceRow) (v : LogFour) : ℝ :=
  currentDensity r v * harmonicDensity v

theorem integrable_weightedMajorant (r : SourceRow) :
    IntegrableOn (weightedMajorant r) (fullParent r) := by
  have h := (integrable_unweightedDensity_fullParent r).const_mul
    (currentSavedParent r / parentUnweightedMass (fullParent r))
  convert h using 1
  ext v
  dsimp [weightedMajorant, currentDensity]
  ring

theorem weightedMajorant_full_integral (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    (∫ v in fullParent r, weightedMajorant r v) = currentSavedParent r := by
  have heq : weightedMajorant r = fun v =>
      (currentSavedParent r / parentUnweightedMass (fullParent r)) * (harmonicDensity v / v 2) := by
    funext v
    dsimp [weightedMajorant, currentDensity]
    ring
  rw [heq, integral_const_mul]
  exact div_mul_cancel₀ _ (retained_reference_mass_pos r hr).ne'

theorem retained_cost_pointwise_le_majorant (r : SourceRow) (hr : r ∈ actualRetainedRows)
    {v : LogFour} (hv : v ∈ fullParent r) :
    cost ImbalancedChen.currentK v * harmonicDensity v ≤ weightedMajorant r v := by
  have ht := (P2N48ActualGeometricKeyDecoder.decoded_of_mem_rawSelectedRows r
    (actualRetainedRows_policy r hr).1).1
  have hD : v ∈ originalDomain ∅ := by
    simpa only [fullParent, if_neg (by omega : ¬r.term.val = 0)] using hv.2
  exact mul_le_mul_of_nonneg_right
    ((cost_bounds_on_original ImbalancedChen.currentK (by norm_num [ImbalancedChen.currentK])
      ∅ v hD).2.trans (retained_current_pointwise_majorant_proposal r hr hv))
    (P5Z.U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hD)

/-- Restrict the existing saved majorant to the EXACT adopted complement.
All removed switched mass is paid from that SAME parent ledger. The
minimum-to-switch upper inequality is used only in its valid direction. -/
theorem same_mask_saved_cost_with_removed_switch_proposal (r : SourceRow)
    (hr : r ∈ actualRetainedRows) :
    parentCost ImbalancedChen.currentK (selectedParent r actualMask) +
      (∫ v in fullParent r \ selectedParent r actualMask,
        switchedKernel ImbalancedChen.currentK buchstab v * harmonicDensity v) ≤
      currentSavedParent r := by
  let S := selectedParent r actualMask
  let D := fullParent r \ S
  have hsub : S ⊆ fullParent r := selectedParent_subset_fullParent r actualMask
  have hS : MeasurableSet S := measurableSet_selectedParent r
  have hD : MeasurableSet D := (measurableSet_fullParent r).diff hS
  have hiM := integrable_weightedMajorant r
  have hiS := (integrable_cost_fullParent r).mono_set hsub
  have hiW : IntegrableOn (fun v => switchedKernel ImbalancedChen.currentK buchstab v *
      harmonicDensity v) (fullParent r) := by
    have h := (integrable_switch_fullParent r).const_mul ImbalancedChen.currentK
    convert h using 1
    ext v
    rw [switchedKernel_eq_mul_base]
    ring
  have hcost := setIntegral_mono_on hiS (hiM.mono_set hsub) hS
    (fun v hv => retained_cost_pointwise_le_majorant r hr (hsub hv))
  have hswitch := setIntegral_mono_on (hiW.mono_set (show D ⊆ fullParent r from fun _ h => h.1))
    (hiM.mono_set (show D ⊆ fullParent r from fun _ h => h.1)) hD (fun v hv => by
      have h0 := row_coordinate_pos r v hv.1 0
      have h1 := row_coordinate_pos r v hv.1 1
      have h2 := row_coordinate_pos r v hv.1 2
      have h3 := row_coordinate_pos r v hv.1 3
      have hdensity : 0 ≤ harmonicDensity v := by unfold harmonicDensity; positivity
      exact mul_le_mul_of_nonneg_right
        (retained_current_pointwise_majorant_proposal r hr hv.1) hdensity)
  have hdisj : Disjoint S D := Set.disjoint_left.mpr (fun _ hs hd => hd.2 hs)
  have hunion : S ∪ D = fullParent r := by
    ext v
    simp only [D, Set.mem_union, Set.mem_diff]
    constructor
    · rintro (hs | hd)
      · exact hsub hs
      · exact hd.1
    · intro hv
      by_cases hs : v ∈ S
      · exact Or.inl hs
      · exact Or.inr ⟨hv, hs⟩
  have hsplit := setIntegral_union hdisj hD (hiM.mono_set hsub)
    (hiM.mono_set (show D ⊆ fullParent r from fun _ h => h.1))
  rw [hunion, weightedMajorant_full_integral r hr] at hsplit
  change (∫ v in S, cost ImbalancedChen.currentK v * harmonicDensity v) +
    (∫ v in D, switchedKernel ImbalancedChen.currentK buchstab v * harmonicDensity v) ≤ _
  linarith only [hcost, hswitch, hsplit]

/-- Actual retained source family, with the old row gain booked once.
Uncovered parents and U10 remain outside this selected-family statement. -/
theorem actual_retained_same_mask_payment_proposal :
    (∑ r ∈ actualRetainedRows,
      parentCost ImbalancedChen.currentK (selectedParent r actualMask)) +
    (∑ r ∈ actualRetainedRows, ∫ v in fullParent r \ selectedParent r actualMask,
      switchedKernel ImbalancedChen.currentK buchstab v * harmonicDensity v) ≤
    (∑ r ∈ actualRetainedRows, savedParent r (parentUnweightedMass (fullParent r))) -
      ∑ r ∈ actualRetainedRows, rowGainLower r := by
  have h := Finset.sum_le_sum (fun r hr => same_mask_saved_cost_with_removed_switch_proposal r hr)
  simpa only [Finset.sum_add_distrib, currentSavedParent, Finset.sum_sub_distrib] using h

end
end ImbalancedChen.P2N48OriginalPointwiseSavedMajorant
