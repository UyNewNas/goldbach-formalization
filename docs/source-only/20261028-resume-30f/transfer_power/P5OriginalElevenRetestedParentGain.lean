import ImbalancedChen.P5OriginalCommonRefinedConstructor
import ImbalancedChen.P5ActualCommonRefinedRange

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original saving #7: exact comparison between its independently defined
archived oldCap->newCap rational profile and the actual re-tested common
fifth parent -> actual all11 maximum profile. The two additional profile
terms retain the changed-parent and simultaneous-maximum differences.
The true old-parent re-test is never deleted: a PhysicalCell whose actual
parent exceeds oldCap is explicitly excluded. Nothing proves that this
excluded carrier is empty, or that archived same-domain gains survive
unconditionally. No full22/full87 or licensed Family cover is assumed.
-/
namespace ImbalancedChen.P5Z.OriginalElevenRetestedParentGain
noncomputable section
open Classical
open scoped BigOperators
open P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor
open Certificates.P2OriginalSixthElevenLogSemantics

/-- The archived comparison cap and actual common fifth parent are
separate independent quantities even at the same original source tuple. -/
theorem actual_retest_exact (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hlen : pre.length = 6) (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre)) :
    eligibleSixth d N c pre ↔
      H5 (primeHistoryLogCoordinates N 6 pre) < actualParent5 d N pre ∧
        actualParent5 d N pre ≤ oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  simp only [eligibleSixth, hlen, hc, true_and]

theorem original_cell_excluded_when_parent_exceeds_comparison
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hparent : oldCap c (primeHistoryLogCoordinates N 6 pre) < actualParent5 d N pre) :
    ¬eligibleSixth d N c pre := by
  intro h
  exact (not_le_of_gt hparent) h.2.2.2

/-- The history guard already present in the actual re-test pays the
ordinary initial lower residual bound at THIS fifth parent. -/
theorem eligible_actual_parent_residual_gt_last
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hc : eligibleSixth d N c pre) :
    (primeHistoryLogCoordinates N 6 pre) 5 <
      actualParent5 d N pre-S6 (primeHistoryLogCoordinates N 6 pre) := by
  have hh := hc.2.2.1
  have ho := hc.2.1.order.1
  dsimp [H5, S6, S5] at hh ⊢
  linarith

/-- All simultaneously eligible source rows share the actual tuple and
its original last-prime cutoff. Their finite maximum stays in the SAME
ordinary initial residual interval; no future parent is substituted. -/
theorem eligible_actual_max_residual_range
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hc : eligibleSixth d N c pre) :
    let t := primeHistoryLogCoordinates N 6 pre
    t 5 < lambda6 d N pre-S6 t ∧ lambda6 d N pre-S6 t ≤ 3*t 5 := by
  let t := primeHistoryLogCoordinates N 6 pre
  have hl := eligible_actual_parent_residual_gt_last d N c pre hc
  have hs := actualParent5_le_lambda6 d N pre
  have hold := hc.2.2.2
  have hgap := hc.2.1.positiveGap
  have hnew := hc.2.1.newArgument
  change newCap c t-S6 t < 3*t 5 at hnew
  have hupper : lambda6 d N pre ≤ S6 t+3*t 5 := by
    unfold lambda6
    apply finiteMax_le _ _ _ _ _ (by linarith)
    intro c' hc' heligible
    have harg := heligible.2.1.newArgument
    change newCap c' t-S6 t < 3*t 5 at harg
    linarith
  exact ⟨by linarith, by linarith⟩

/-- Elementary rational identity on this very source profile; its
ordinary-density meaning requires the residual interval proved above. -/
theorem three_cap_profile_telescope {k : ℕ} (t : Fin k → ℝ) (L R M : ℝ)
    (hL : L-∑ i,t i ≠ 0) (hR : R-∑ i,t i ≠ 0) (hM : M-∑ i,t i ≠ 0) :
    primeBoxInitialSavingProfile L M t =
      primeBoxInitialSavingProfile L R t+primeBoxInitialSavingProfile R M t := by
  unfold primeBoxInitialSavingProfile
  field_simp [hL,hR,hM]
  ring

/-- Both extra terms are kept, rather than quietly equating the archive's
old comparison with the new common parent or its selected maximum. -/
theorem actual_profile_minus_archived_profile
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hc : eligibleSixth d N c pre) :
    let t := primeHistoryLogCoordinates N 6 pre
    primeBoxInitialSavingProfile (actualParent5 d N pre) (lambda6 d N pre) t-
      primeBoxInitialSavingProfile (oldCap c t) (newCap c t) t =
        primeBoxInitialSavingProfile (actualParent5 d N pre) (oldCap c t) t+
          primeBoxInitialSavingProfile (newCap c t) (lambda6 d N pre) t := by
  let t := primeHistoryLogCoordinates N 6 pre
  have hlast := hc.2.1.rpos
  have hL := eligible_actual_parent_residual_gt_last d N c pre hc
  have hR := hc.2.1.residual_guards.2.1
  have hM := hc.2.1.residual_guards.2.2.1
  have hU := actualParent5_le_lambda6 d N pre
  have hR0 : 0 < oldCap c t-S6 t := by
    change t 5 < oldCap c t-S6 t at hR
    linarith
  have hM0 : 0 < newCap c t-S6 t := by
    change oldCap c t-S6 t < newCap c t-S6 t at hM
    linarith
  have hL0 : 0 < actualParent5 d N pre-S6 t := by linarith
  have hU0 : 0 < lambda6 d N pre-S6 t := by linarith
  have hsum := S6_eq_sum t
  have h1 := three_cap_profile_telescope t (actualParent5 d N pre) (oldCap c t)
    (lambda6 d N pre) (by rw [←hsum]; exact hL0.ne')
    (by rw [←hsum]; exact hR0.ne') (by rw [←hsum]; exact hU0.ne')
  have h2 := three_cap_profile_telescope t (oldCap c t) (newCap c t) (lambda6 d N pre)
    (by rw [←hsum]; exact hR0.ne') (by rw [←hsum]; exact hM0.ne')
    (by rw [←hsum]; exact hU0.ne')
  linarith

theorem actual_profile_minus_archived_nonneg
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hc : eligibleSixth d N c pre) :
    let t := primeHistoryLogCoordinates N 6 pre
    0 ≤ primeBoxInitialSavingProfile (actualParent5 d N pre) (lambda6 d N pre) t-
      primeBoxInitialSavingProfile (oldCap c t) (newCap c t) t := by
  rw [actual_profile_minus_archived_profile d N c pre hc]
  let t := primeHistoryLogCoordinates N 6 pre
  have hL := eligible_actual_parent_residual_gt_last d N c pre hc
  have hlast := hc.2.1.rpos
  have hparent := hc.2.2.2
  have hnew := eligibleSixth_newCap_le_lambda6 d N c pre hc
  have hgap := hc.2.1.positiveGap
  have hsum := S6_eq_sum t
  unfold primeBoxInitialSavingProfile
  rw [←hsum]
  apply add_nonneg
  · apply div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hparent))
    apply mul_nonneg <;> linarith
  · apply div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hnew))
    apply mul_nonneg <;> linarith

/-- The same source coordinate product and ordered occurrence density as
in the archive's savingKernel. No permutation or Chen-quarter factor. -/
def actualRetestedKernel (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 6 pre
  primeBoxInitialSavingProfile (actualParent5 d N pre) (lambda6 d N pre) t/coordinateProduct t

theorem actual_kernel_minus_archived_exact
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hc : eligibleSixth d N c pre) :
    let t := primeHistoryLogCoordinates N 6 pre
    actualRetestedKernel d N pre-savingKernel c t =
      (primeBoxInitialSavingProfile (actualParent5 d N pre) (oldCap c t) t+
        primeBoxInitialSavingProfile (newCap c t) (lambda6 d N pre) t)/coordinateProduct t := by
  rw [savingKernel_eq_actual_profile]
  change _/_- _/_ = _
  rw [←sub_div, actual_profile_minus_archived_profile d N c pre hc]

theorem archived_kernel_le_actual_retested_kernel
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hc : eligibleSixth d N c pre) :
    savingKernel c (primeHistoryLogCoordinates N 6 pre) ≤ actualRetestedKernel d N pre := by
  have hprofile := actual_profile_minus_archived_nonneg d N c pre hc
  have hprod := hc.2.1.coordinateProduct_pos
  apply sub_nonneg.mp
  rw [actual_kernel_minus_archived_exact d N c pre hc]
  have hid := actual_profile_minus_archived_profile d N c pre hc
  rw [←hid]
  exact div_nonneg hprofile hprod.le

end
end ImbalancedChen.P5Z.OriginalElevenRetestedParentGain
