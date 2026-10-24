import ImbalancedChen.Part5Family3947Geometry

/-!
SOURCE ONLY / UNCOMPILED.

Dependency recipe: install the 20261024y All32 assembly as
ImbalancedChen.Part5SavedParent394700Buchstab, and the existing
20261024-P5-family3947-modular-assembly-SOURCEONLY Geometry candidate as
ImbalancedChen.Part5Family3947Geometry. This file adds no enclosure cells,
coordinates, original constants, or arithmetic-parent assertion.

The family geometry already identifies its first public parent with the
concrete All32 parent. These lemmas transport the concrete density licence
through that equality and through arbitrary crops of the public parent.
-/

namespace ImbalancedChen.Certificates.P0All32ParentPublicAPI

open Set MeasureTheory

noncomputable section


/-- Original weak-index parent [1,39,47,0,0], using the existing index type. -/
abbrev originalParent : SavedParentFamily3947SourceOnly.ParentIndex := ⟨0, 0, by decide⟩

/-- The scalar density bound in the public family's argument convention. -/
theorem savedDensity_ge_actual_on_public_parent
    {p : Fin 4 → ℝ} (hp : p ∈ SavedParentFamily3947SourceOnly.parentClosure originalParent) :
    SavedParent394700SourceOnly.K * LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) / p 2 ≤
      SavedParent394700SourceOnly.savedDensity (p 2) := by
  have hc : p ∈ SavedParent394700SourceOnly.parentClosure := by
    rw [← SavedParentFamily3947SourceOnly.first_original_parent_closed_domain_exact]
    exact hp
  simpa only [SavedParentFamily3947SourceOnly.argument, SavedParent394700SourceOnly.argument] using
    SavedParent394700SourceOnly.original_savedDensity_ge_actual_on_parent hc

/-- The literal Chen-quarter comparison on the public closed parent. -/
theorem savedChenDensity_ge_actual_on_public_parent
    {p : Fin 4 → ℝ} (hp : p ∈ SavedParentFamily3947SourceOnly.parentClosure originalParent) :
    (SavedParent394700SourceOnly.K / 4) * LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3) ≤ SavedParent394700SourceOnly.savedChenDensity p := by
  have hc : p ∈ SavedParent394700SourceOnly.parentClosure := by
    rw [← SavedParentFamily3947SourceOnly.first_original_parent_closed_domain_exact]
    exact hp
  simpa only [SavedParentFamily3947SourceOnly.argument, SavedParent394700SourceOnly.argument] using
    SavedParent394700SourceOnly.original_savedChenDensity_ge_actual_kernel hc

theorem savedDensity_ge_actual_on_public_open_parent
    {p : Fin 4 → ℝ} (hp : p ∈ SavedParentFamily3947SourceOnly.parentOpen originalParent) :
    SavedParent394700SourceOnly.K * LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) / p 2 ≤
      SavedParent394700SourceOnly.savedDensity (p 2) := by
  exact savedDensity_ge_actual_on_public_parent
    (SavedParentFamily3947SourceOnly.parentOpen_subset_closure originalParent hp)

theorem savedChenDensity_ge_actual_on_public_open_parent
    {p : Fin 4 → ℝ} (hp : p ∈ SavedParentFamily3947SourceOnly.parentOpen originalParent) :
    (SavedParent394700SourceOnly.K / 4) * LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3) ≤ SavedParent394700SourceOnly.savedChenDensity p := by
  exact savedChenDensity_ge_actual_on_public_parent
    (SavedParentFamily3947SourceOnly.parentOpen_subset_closure originalParent hp)

/-- No geometric property of the crop is needed for the pointwise licence. -/
theorem savedDensity_ge_actual_on_public_crop
    (crop : Set (Fin 4 → ℝ)) {p : Fin 4 → ℝ}
    (hp : p ∈ SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop) :
    SavedParent394700SourceOnly.K * LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) / p 2 ≤
      SavedParent394700SourceOnly.savedDensity (p 2) := by
  exact savedDensity_ge_actual_on_public_parent hp.1

theorem savedChenDensity_ge_actual_on_public_crop
    (crop : Set (Fin 4 → ℝ)) {p : Fin 4 → ℝ}
    (hp : p ∈ SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop) :
    (SavedParent394700SourceOnly.K / 4) * LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3) ≤ SavedParent394700SourceOnly.savedChenDensity p := by
  exact savedChenDensity_ge_actual_on_public_parent hp.1

/-- Indicator comparison for consumers extending a cropped kernel by zero. -/
theorem public_crop_indicator_le (crop : Set (Fin 4 → ℝ)) (p : Fin 4 → ℝ) :
    (SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop).indicator
      (fun q => (SavedParent394700SourceOnly.K / 4) *
        LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument q) *
        pairedFibreKernel (q 0) (q 1) (q 2) (q 3)) p ≤
    (SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop).indicator
      SavedParent394700SourceOnly.savedChenDensity p := by
  classical
  by_cases hp : p ∈ SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop
  · simp only [Set.indicator_of_mem hp]
    exact savedChenDensity_ge_actual_on_public_crop crop hp
  · simp only [Set.indicator_of_notMem hp]
    exact le_refl 0

/-- The pointwise licence also works directly on a retained subregion. -/
theorem savedChenDensity_ge_actual_on_retained_region
    {region : Set (Fin 4 → ℝ)}
    (hregion : region ⊆ SavedParentFamily3947SourceOnly.parentClosure originalParent)
    {p : Fin 4 → ℝ} (hp : p ∈ region) :
    (SavedParent394700SourceOnly.K / 4) * LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3) ≤ SavedParent394700SourceOnly.savedChenDensity p := by
  exact savedChenDensity_ge_actual_on_public_parent (hregion hp)

/-- Integrable kernels on a measurable retained region inherit the proved
pointwise inequality. These are analytic well-definedness hypotheses, not
an assumed Buchstab enclosure or saved-density domination. -/
theorem actual_integral_le_savedChenDensity_on_retained_region
    {region : Set (Fin 4 → ℝ)}
    (hregion : region ⊆ SavedParentFamily3947SourceOnly.parentClosure originalParent)
    (hregion_meas : MeasurableSet region)
    (hactual : IntegrableOn
      (fun p => (SavedParent394700SourceOnly.K / 4) *
        LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
        pairedFibreKernel (p 0) (p 1) (p 2) (p 3)) region)
    (hsaved : IntegrableOn SavedParent394700SourceOnly.savedChenDensity region) :
    (∫ p in region, (SavedParent394700SourceOnly.K / 4) *
      LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3)) ≤
      ∫ p in region, SavedParent394700SourceOnly.savedChenDensity p := by
  apply MeasureTheory.setIntegral_mono_on hactual hsaved hregion_meas
  intro p hp
  exact savedChenDensity_ge_actual_on_retained_region hregion hp

theorem actual_integral_le_savedChenDensity_on_public_crop
    (crop : Set (Fin 4 → ℝ))
    (hregion_meas : MeasurableSet (SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop))
    (hactual : IntegrableOn
      (fun p => (SavedParent394700SourceOnly.K / 4) *
        LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
        pairedFibreKernel (p 0) (p 1) (p 2) (p 3))
      (SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop))
    (hsaved : IntegrableOn SavedParent394700SourceOnly.savedChenDensity
      (SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop)) :
    (∫ p in SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop, (SavedParent394700SourceOnly.K / 4) *
      LiLiuPrereqBuchstab.buchstab (SavedParentFamily3947SourceOnly.argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3)) ≤
      ∫ p in SavedParentFamily3947SourceOnly.parentClosure originalParent ∩ crop,
        SavedParent394700SourceOnly.savedChenDensity p := by
  exact actual_integral_le_savedChenDensity_on_retained_region
    Set.inter_subset_left hregion_meas hactual hsaved

end

end ImbalancedChen.Certificates.P0All32ParentPublicAPI
