import ImbalancedChen.Part5Family3947Geometry
import Mathlib.Tactic.FunProp

/-! SOURCE ONLY / UNCOMPILED.
Uses the existing All32 and family Geometry candidates. All real functions
below are the original saved-density definitions. Compactness is proved on
the actual seven-inequality parent; no Buchstab integrability is assumed or
proved here. -/

namespace ImbalancedChen.Certificates.P0ParentKernelIntegrabilityAPI

open Set MeasureTheory

noncomputable section

theorem isClosed_concrete_parent :
    IsClosed SavedParent394700SourceOnly.parentClosure := by
  have h0 : Continuous (fun p : Fin 4 → ℝ => p 0) := continuous_apply 0
  have h1 : Continuous (fun p : Fin 4 → ℝ => p 1) := continuous_apply 1
  have h2 : Continuous (fun p : Fin 4 → ℝ => p 2) := continuous_apply 2
  have h3 : Continuous (fun p : Fin 4 → ℝ => p 3) := continuous_apply 3
  exact (isClosed_le continuous_const h0).inter
    ((isClosed_le h0 continuous_const).inter
    ((isClosed_le continuous_const h1).inter
    ((isClosed_le h1 continuous_const).inter
    ((isClosed_le continuous_const h3).inter
    ((isClosed_le h3 h2).inter (isClosed_le h2 continuous_const))))))

theorem measurableSet_concrete_parent :
    MeasurableSet SavedParent394700SourceOnly.parentClosure :=
  isClosed_concrete_parent.measurableSet

/-- The original parent is a closed subset of a fixed compact cube. -/
theorem isCompact_concrete_parent :
    IsCompact SavedParent394700SourceOnly.parentClosure := by
  have hcube : IsCompact
      (Set.univ.pi (fun _ : Fin 4 => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hcube.of_isClosed_subset isClosed_concrete_parent
  intro p hp i _
  have hpos := SavedParent394700SourceOnly.parent_coordinates_pos hp
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have ht : SavedParent394700SourceOnly.tr ≤ 1 := by
    norm_num [SavedParent394700SourceOnly.tr]
  have hu : SavedParent394700SourceOnly.ur ≤ 1 := by
    norm_num [SavedParent394700SourceOnly.ur]
  have hb : SavedParent394700SourceOnly.b ≤ 1 := by
    norm_num [SavedParent394700SourceOnly.b]
  fin_cases i
  · exact ⟨hpos.1.le, h1.trans ht⟩
  · exact ⟨hpos.2.1.le, h3.trans hu⟩
  · exact ⟨hpos.2.2.1.le, h6.trans hb⟩
  · exact ⟨hpos.2.2.2.le, h5.trans (h6.trans hb)⟩

theorem measurable_savedDensity :
    Measurable SavedParent394700SourceOnly.savedDensity := by
  unfold SavedParent394700SourceOnly.savedDensity
  exact measurable_const.div (measurable_const.mul measurable_id)

theorem continuousOn_savedDensity_interval :
    ContinuousOn SavedParent394700SourceOnly.savedDensity
      (Icc SavedParent394700SourceOnly.a SavedParent394700SourceOnly.b) := by
  unfold SavedParent394700SourceOnly.savedDensity
  apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
  intro z hz
  have ha : 0 < SavedParent394700SourceOnly.a := by
    norm_num [SavedParent394700SourceOnly.a]
  exact (mul_pos SavedParent394700SourceOnly.referenceMass_pos
    (ha.trans_le hz.1)).ne'

theorem integrableOn_savedDensity_interval :
    IntegrableOn SavedParent394700SourceOnly.savedDensity
      (Icc SavedParent394700SourceOnly.a SavedParent394700SourceOnly.b) :=
  continuousOn_savedDensity_interval.integrableOn_compact isCompact_Icc

theorem measurable_savedDensity_coordinate :
    Measurable (fun p : Fin 4 → ℝ =>
      SavedParent394700SourceOnly.savedDensity (p 2)) :=
  measurable_savedDensity.comp (measurable_pi_apply 2)

theorem continuousOn_savedDensity_coordinate :
    ContinuousOn (fun p : Fin 4 → ℝ =>
      SavedParent394700SourceOnly.savedDensity (p 2))
      SavedParent394700SourceOnly.parentClosure := by
  unfold SavedParent394700SourceOnly.savedDensity
  apply continuousOn_const.div
    (continuousOn_const.mul (continuous_apply 2).continuousOn)
  intro p hp
  exact (mul_pos SavedParent394700SourceOnly.referenceMass_pos
    (SavedParent394700SourceOnly.parent_coordinates_pos hp).2.2.1).ne'

theorem measurable_savedChenDensity :
    Measurable SavedParent394700SourceOnly.savedChenDensity := by
  have hd : Measurable
      (fun p : Fin 4 → ℝ => 4 * p 0 * p 1 * p 2 * p 3) := by fun_prop
  exact measurable_savedDensity_coordinate.mul (measurable_const.div hd)

theorem continuousOn_savedChenDensity :
    ContinuousOn SavedParent394700SourceOnly.savedChenDensity
      SavedParent394700SourceOnly.parentClosure := by
  have hd : Continuous
      (fun p : Fin 4 → ℝ => 4 * p 0 * p 1 * p 2 * p 3) := by fun_prop
  apply continuousOn_savedDensity_coordinate.mul
    (continuousOn_const.div hd.continuousOn ?_)
  intro p hp
  rcases SavedParent394700SourceOnly.parent_coordinates_pos hp with
    ⟨ht, hu, hz, hw⟩
  exact (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) ht) hu) hz) hw).ne'

theorem integrableOn_savedDensity_coordinate :
    IntegrableOn (fun p : Fin 4 → ℝ =>
      SavedParent394700SourceOnly.savedDensity (p 2))
      SavedParent394700SourceOnly.parentClosure :=
  continuousOn_savedDensity_coordinate.integrableOn_compact isCompact_concrete_parent

theorem integrableOn_savedChenDensity :
    IntegrableOn SavedParent394700SourceOnly.savedChenDensity
      SavedParent394700SourceOnly.parentClosure :=
  continuousOn_savedChenDensity.integrableOn_compact isCompact_concrete_parent

/-- Integrability restricts to any retained region, even before a crop's
measurability is supplied for integral comparison. -/
theorem integrableOn_savedChenDensity_of_subset
    {region : Set (Fin 4 → ℝ)}
    (hregion : region ⊆ SavedParent394700SourceOnly.parentClosure) :
    IntegrableOn SavedParent394700SourceOnly.savedChenDensity region :=
  integrableOn_savedChenDensity.mono_set hregion

abbrev originalParent : SavedParentFamily3947SourceOnly.ParentIndex := ⟨0, 0, by decide⟩

theorem isCompact_public_parent :
    IsCompact (SavedParentFamily3947SourceOnly.parentClosure originalParent) := by
  rw [SavedParentFamily3947SourceOnly.first_original_parent_closed_domain_exact]
  exact isCompact_concrete_parent

theorem measurableSet_public_parent :
    MeasurableSet (SavedParentFamily3947SourceOnly.parentClosure originalParent) :=
  isCompact_public_parent.isClosed.measurableSet

theorem continuousOn_savedDensity_coordinate_public_parent :
    ContinuousOn (fun p : Fin 4 → ℝ =>
      SavedParent394700SourceOnly.savedDensity (p 2))
      (SavedParentFamily3947SourceOnly.parentClosure originalParent) := by
  rw [SavedParentFamily3947SourceOnly.first_original_parent_closed_domain_exact]
  exact continuousOn_savedDensity_coordinate

theorem integrableOn_savedDensity_coordinate_public_parent :
    IntegrableOn (fun p : Fin 4 → ℝ =>
      SavedParent394700SourceOnly.savedDensity (p 2))
      (SavedParentFamily3947SourceOnly.parentClosure originalParent) := by
  rw [SavedParentFamily3947SourceOnly.first_original_parent_closed_domain_exact]
  exact integrableOn_savedDensity_coordinate

theorem continuousOn_savedChenDensity_public_parent :
    ContinuousOn SavedParent394700SourceOnly.savedChenDensity
      (SavedParentFamily3947SourceOnly.parentClosure originalParent) := by
  rw [SavedParentFamily3947SourceOnly.first_original_parent_closed_domain_exact]
  exact continuousOn_savedChenDensity

theorem integrableOn_savedChenDensity_public_parent :
    IntegrableOn SavedParent394700SourceOnly.savedChenDensity
      (SavedParentFamily3947SourceOnly.parentClosure originalParent) := by
  rw [SavedParentFamily3947SourceOnly.first_original_parent_closed_domain_exact]
  exact integrableOn_savedChenDensity

theorem integrableOn_savedChenDensity_public_crop
    (crop : Set (Fin 4 → ℝ)) :
    IntegrableOn SavedParent394700SourceOnly.savedChenDensity
      (SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop) :=
  integrableOn_savedChenDensity_public_parent.mono_set Set.inter_subset_left

/-- The saved-density integrability premise is discharged. The actual
Buchstab kernel retains its separate integrability obligation. -/
theorem actual_integral_le_savedChenDensity_public_crop
    (crop : Set (Fin 4 → ℝ)) (hcrop : MeasurableSet crop)
    (hactual : IntegrableOn
      (fun p => (SavedParent394700SourceOnly.K / 4) *
        LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
        pairedFibreKernel (p 0) (p 1) (p 2) (p 3))
      (SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop)) :
    (∫ p in SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop,
      (SavedParent394700SourceOnly.K / 4) *
        LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
        pairedFibreKernel (p 0) (p 1) (p 2) (p 3)) ≤
    ∫ p in SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop,
      SavedParent394700SourceOnly.savedChenDensity p := by
  apply MeasureTheory.setIntegral_mono_on hactual
    (integrableOn_savedChenDensity_public_crop crop)
    (measurableSet_public_parent.inter hcrop)
  intro p hp
  have hparent : p ∈ SavedParent394700SourceOnly.parentClosure := by
    rw [← SavedParentFamily3947SourceOnly.first_original_parent_closed_domain_exact]
    exact hp.1
  simpa only [SavedParentFamily3947SourceOnly.argument,
    SavedParent394700SourceOnly.argument] using
    SavedParent394700SourceOnly.original_savedChenDensity_ge_actual_kernel hparent

end

end ImbalancedChen.Certificates.P0ParentKernelIntegrabilityAPI
