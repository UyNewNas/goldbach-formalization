import ImbalancedChen.P2N48OriginalPointwiseSavedMajorant
import ImbalancedChen.P2FullMaskActualNativeGain
import ImbalancedChen.P5ZU1011OriginalPairedFixedMaskHarmonic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
All sixteen ORIGINAL ordinary policies fail their final full-square gate
on every actually adopted pair rectangle. The coarse coordinate minima
already give a strict gap, so no new row enumeration or 9/4 check is needed.
This proves a true equality with the switched kernel on the deleted region;
it does not reverse actualMinimum <= switched.
-/
namespace ImbalancedChen.P2ActualCropOrdinaryExclusion
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P5Z.U11Integral P5Z.U11Canonical
open P5Z.U1011OriginalSixteenPolicyBank P5Z.U1011OriginalSixteenAnchorFeedback
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P5Z.U1011OriginalPairedRowPrimeTests

theorem original_policy_cap_le (p : Policy) (v : LogFour) (hv2 : 0 ≤ v 2) :
    cap p v ≤ (153 / 256 : ℝ) := by
  by_cases hp : p.val < 15
  · unfold cap
    rw [if_pos hp]
    by_cases hs : selectedMass p v ≤ (25 / 128 : ℝ)
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  · unfold cap
    rw [if_neg hp]
    linarith

/-- Coarse bounds valid on ALL actual rows, including their lower faces.
The imported firstU_bounds is the existing literal-mask proposal. -/
theorem actual_pair_coordinate_lower (r : FullMask.Row) {v : LogFour}
    (hv : v ∈ rowRegion r) :
    (tLower 326 : ℝ) ≤ v 0 ∧ (uLower 321 : ℝ) ≤ v 1 := by
  have hi : 326 ≤ (indices r).1 := by simp only [indices]; omega
  have hj : 321 ≤ (indices r).2 := by
    have h := (firstU_bounds r.1).1
    simp only [indices]
    omega
  have hiR : (326 : ℝ) ≤ (indices r).1 := by exact_mod_cast hi
  have hjR : (321 : ℝ) ≤ (indices r).2 := by exact_mod_cast hj
  have ht : (tLower 326 : ℝ) ≤ (tLower (indices r).1 : ℝ) := by
    norm_num [tLower, mu, d]
    linarith only [hiR]
  have hu : (uLower 321 : ℝ) ≤ (uLower (indices r).2 : ℝ) := by
    norm_num [uLower, a, h]
    linarith only [hjR]
  exact ⟨ht.trans hv.1, hu.trans hv.2.2.1⟩

/-- The strict gap uses the literal global minima 326 and 321. It covers
the WHOLE original a<=w<z<u fibre, not merely the extra Z_B subfibre. -/
theorem actual_crop_last_square_gt (r : FullMask.Row) {v : LogFour}
    (hv : v ∈ P5Z.U1011OriginalPairedFixedMaskHarmonic.rowDomain r) :
    (153 / 256 : ℝ) < fullSquare 3 v := by
  have hxy := actual_pair_coordinate_lower r hv.2
  have hw : (417 / 5000 : ℝ) ≤ v 3 := hv.1.1
  have hz : v 3 < v 2 := hv.1.2.1
  have hgap : (153 / 256 : ℝ) < (tLower 326 : ℝ) + (uLower 321 : ℝ) +
      3 * (417 / 5000 : ℝ) := by
    norm_num [tLower, uLower, mu, d, a, h]
  rw [fullSquare_last]
  dsimp [P5Z.U11SelectedLargest.prefixSum]
  linarith only [hxy.1, hxy.2, hw, hz, hgap]

theorem actual_crop_no_typed_ordinary (r : FullMask.Row) (p : Policy) {v : LogFour}
    (hv : v ∈ P5Z.U1011OriginalPairedFixedMaskHarmonic.rowDomain r) :
    ¬TypedEligible p v := by
  intro he
  have hz : 0 ≤ v 2 := by linarith [hv.1.1, hv.1.2.1]
  have hc := original_policy_cap_le p v hz
  have hl := actual_crop_last_square_gt r hv
  exact (not_lt_of_ge (hc.trans hl.le)) (he.2.1 3)

theorem actual_crop_no_ordinary (r : FullMask.Row) (j : ℕ) {v : LogFour}
    (hv : v ∈ P5Z.U1011OriginalPairedFixedMaskHarmonic.rowDomain r) :
    ¬eligible j v := by
  by_cases hj : j < 16
  · simpa only [eligible, dif_pos hj] using actual_crop_no_typed_ordinary r ⟨j,hj⟩ hv
  · simp only [eligible, dif_neg hj, not_false_eq_true]

theorem cost_eq_switched_on_actual_row (k : ℝ) (r : FullMask.Row) {v : LogFour}
    (hv : v ∈ P5Z.U1011OriginalPairedFixedMaskHarmonic.rowDomain r) :
    cost k v = switchedKernel k LiLiuPrereqBuchstab.buchstab v := by
  apply cost_eq_switched_on_anchor (k0 := k) le_rfl ∅ v hv.1
  intro j _ he
  exact (actual_crop_no_ordinary r j hv he).elim

theorem cost_eq_switched_on_actual_deleted (k : ℝ) {v : LogFour}
    (hv : v ∈ P5Z.U1011OriginalPairedFixedMaskHarmonic.domain ∩
      P5Z.U1011OriginalPairedFixedMaskHarmonic.removedRegion (Finset.univ : Finset FullMask.Row)) :
    cost k v = switchedKernel k LiLiuPrereqBuchstab.buchstab v := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hv.2
  obtain ⟨_, hrv⟩ := Set.mem_iUnion.mp hr
  exact cost_eq_switched_on_actual_row k r ⟨hv.1, hrv⟩

/-- The original nonlinear row integral is now identified with its
switched integral by a proved gate failure, before any mean is taken. -/
theorem actual_rowIntegral_eq_switched (r : FullMask.Row) :
    P5Z.U1011OriginalPairedFixedMaskHarmonic.rowIntegral r =
      ∫ v in P5Z.U1011OriginalPairedFixedMaskHarmonic.rowDomain r,
        switchedKernel ImbalancedChen.currentK LiLiuPrereqBuchstab.buchstab v * harmonicDensity v := by
  apply setIntegral_congr_fun (P5Z.U1011OriginalPairedFixedMaskHarmonic.measurableSet_rowDomain r)
  intro v hv
  change cost ImbalancedChen.currentK v * harmonicDensity v = _
  rw [cost_eq_switched_on_actual_row ImbalancedChen.currentK r hv]

/-- Exact same-mask cost subtraction. The switch identity is used on
the original deleted rows; U10 is not altered by this high-band identity. -/
theorem actual_mask_cost_subtraction :
    P5Z.U1011OriginalPairedFixedMaskHarmonic.keptIntegral (Finset.univ : Finset FullMask.Row) =
      (∫ v in P5Z.U1011OriginalPairedFixedMaskHarmonic.domain,
        P5Z.U1011OriginalPairedFixedMaskHarmonic.weighted v) -
      ∑ r : FullMask.Row, ∫ v in P5Z.U1011OriginalPairedFixedMaskHarmonic.rowDomain r,
        switchedKernel ImbalancedChen.currentK LiLiuPrereqBuchstab.buchstab v * harmonicDensity v := by
  rw [P5Z.U1011OriginalPairedFixedMaskHarmonic.keptIntegral_eq_difference]
  simp_rw [actual_rowIntegral_eq_switched]

theorem extra_fibre_mem_actual_row (r : FullMask.Row) {v : LogFour}
    (hv : v ∈ FullMask.support r) :
    v ∈ P5Z.U1011OriginalPairedFixedMaskHarmonic.rowDomain r := by
  exact ⟨P2FullMaskN48DeletedOwner.fibre_mem_full_high_domain hv,
    FullMask.P1E0E1.fibre_mem_pairCell hv⟩

/-- G's actual archived owner belongs to the SAME retained method0 family
used by the literal Q112 receiver. Priority replacement is excluded using
its original ordinal; no new choice of parent is made. -/
theorem archived_owner_mem_retained (s : P2FullMaskN48DeletedOwner.ArchivedRow) :
    s.val ∈ P2N48ActualSixteenCostRowAttachment.actualRetainedRows := by
  have hp := P2FullMaskN48DeletedOwner.archived_source_method_and_priority s
  apply (P2N48SavedParentRowRecost.mem_retainedMethodZero _ _ _ _).2
  exact ⟨s.property, s.property, hp.1, hp.2.2⟩

theorem archived_owner_current_pointwise_majorant
    (s : P2FullMaskN48DeletedOwner.ArchivedRow) {v : LogFour}
    (hv : v ∈ P2N48ActualSixteenCostRowAttachment.fullParent s.val) :
    switchedKernel ImbalancedChen.currentK LiLiuPrereqBuchstab.buchstab v ≤
      P2N48OriginalPointwiseSavedMajorant.currentDensity s.val v :=
  P2N48OriginalPointwiseSavedMajorant.retained_current_pointwise_majorant_proposal
    s.val (archived_owner_mem_retained s) hv

/-- Every actual extra-fibre point has its unique old archived owner,
whose positive current density majorizes the actual minimum there. -/
theorem extra_fibre_has_licensed_original_owner (r : FullMask.Row) {v : LogFour}
    (hv : v ∈ FullMask.support r) :
    ∃ s : P2FullMaskN48DeletedOwner.ArchivedRow,
      v ∈ P2N48ActualSixteenCostRowAttachment.fullParent s.val ∧
      cost ImbalancedChen.currentK v =
        switchedKernel ImbalancedChen.currentK LiLiuPrereqBuchstab.buchstab v ∧
      switchedKernel ImbalancedChen.currentK LiLiuPrereqBuchstab.buchstab v ≤
        P2N48OriginalPointwiseSavedMajorant.currentDensity s.val v := by
  obtain ⟨s, hs⟩ := P2FullMaskN48DeletedOwner.exists_archived_full_parent hv
  exact ⟨s, hs, cost_eq_switched_on_actual_row ImbalancedChen.currentK r
    (extra_fibre_mem_actual_row r hv), archived_owner_current_pointwise_majorant s hs⟩

/-- H's actual extra-fibre profile is precisely the true original
nonlinear cost above its already paid half-baseline, in Chen-quarter units. -/
theorem semanticKernel_eq_actual_cost_extra (r : FullMask.Row) {v : LogFour}
    (hv : v ∈ FullMask.support r) :
    FullMask.P2SemanticGainSetIntegral.semanticKernel v =
      (cost ImbalancedChen.currentK v - ImbalancedChen.currentK / (2 * v 2)) *
        harmonicDensity v / 4 := by
  rw [cost_eq_switched_on_actual_row ImbalancedChen.currentK r (extra_fibre_mem_actual_row r hv)]
  rw [← P2FullMaskActualNativeGain.gainProfile_weighted]
  rw [← P5Z.U1011OriginalSixteenFullHarmonic.harmonicDensity_eq_prod]
  dsimp [P2FullMaskActualNativeGain.gainProfile,
    FullMask.P2SemanticGainSetIntegral.gain,
    Certificates.P2HistoricalFibreBinding.pairedSemanticBuchstabGain, switchedKernel]
  have harg : (1 - v 0 - v 1 - v 2 - v 3) / v 2 =
      (1 - (v 0 + v 1 + v 2 + v 3)) / v 2 := by ring
  rw [harg]
  norm_num [Certificates.PairedV2.K, ImbalancedChen.currentK]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem actual_extra_gain_eq_cost_excess :
    P2ActualSameMaskFloorFibreAccounting.actualExtraFibreGain =
      ∫ v in FullMask.region,
        (cost ImbalancedChen.currentK v - ImbalancedChen.currentK / (2 * v 2)) *
          harmonicDensity v / 4 := by
  change (∫ v in FullMask.region, FullMask.P2SemanticGainSetIntegral.semanticKernel v) = _
  apply setIntegral_congr_fun FullMask.P2AdoptedUnion.region_measurable
  intro v hv
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hv
  exact semanticKernel_eq_actual_cost_extra r hr

end
end ImbalancedChen.P2ActualCropOrdinaryExclusion
