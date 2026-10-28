import ImbalancedChen.Part3OriginalActualProductBoundDifferences
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
The prefix envelope is a maximum of the ACTUAL finite coeff5 values,
not an assumed spectral bound. The weight cost is the ACTUAL weight5
variation on the tight physical H box. This gives an unconditional
finite norm/counting source for the later bare spectral deduction.
No scale saving or final variation payment is asserted by definition.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalShiftReindex
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveAbelTower
open ImbalancedChen.Part3.OriginalMediumOneTimeVariationTransfer
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028
open ImbalancedChen.Part3.OriginalPoissonSourceCorrections20261028
open ImbalancedChen.Part3.OriginalSourcePhysicalAbelCaller20261028
open ImbalancedChen.Part3.OriginalActualPoissonTightH20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalActualAbelPrefixCost20261028

attribute [local instance] Classical.propDecidable

def actualPrefixValues (B : FixedBlock) : Finset ℝ :=
  insert 0 ((box B).image (fun r => ‖value (coeff5 B) r‖))

def actualPrefixEnvelope (B : FixedBlock) : ℝ :=
  (actualPrefixValues B).max' ⟨0, by simp [actualPrefixValues]⟩

theorem actualPrefixEnvelope_nonneg (B : FixedBlock) : 0 ≤ actualPrefixEnvelope B := by
  exact Finset.le_max' (actualPrefixValues B) 0 (by simp [actualPrefixValues])

theorem actual_coeff5_le_prefixEnvelope (B : FixedBlock) (r : Raw5) (hr : r ∈ box B) :
    ‖value (coeff5 B) r‖ ≤ actualPrefixEnvelope B := by
  apply Finset.le_max'
  apply Finset.mem_insert.mpr
  exact Or.inr (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

theorem actual_weight5_variation_nonneg (B : FixedBlock) : 0 ≤ variation B (weight5 B) := by
  unfold variation
  exact Finset.sum_nonneg (fun r hr => norm_nonneg _)

def actualTightAbelCost {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) : ℝ :=
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
  if OrderedBox B ∧ 1 ≤ B.H then actualPrefixEnvelope T * variation T (weight5 T) else 0

theorem actualTightAbelCost_nonneg {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    0 ≤ actualTightAbelCost atom z y k hA Csep j small hd negative := by
  unfold actualTightAbelCost
  split_ifs
  · exact mul_nonneg (actualPrefixEnvelope_nonneg _) (actual_weight5_variation_nonneg _)
  · exact le_rfl

/-- The finite prefix bound is DERIVED from its true maximum, rather
than supplied as a final rectangular/bare spectral conclusion. -/
theorem norm_actual_E3_le_tightAbelCost {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool) :
    ‖(poissonAtlasBlock atom z y k hA Csep j small hd negative).E3‖ ≤
      actualTightAbelCost atom z y k hA Csep j small hd negative := by
  let B := poissonAtlasBlock atom z y k hA Csep j small hd negative
  let T := tightPoissonAtlasBlock atom z y k hA Csep j small hd negative
  change ‖B.E3‖ ≤ if OrderedBox B ∧ 1 ≤ B.H then
    actualPrefixEnvelope T * variation T (weight5 T) else 0
  by_cases hv : OrderedBox B ∧ 1 ≤ B.H
  · rw [if_pos hv]
    have hp := tightPoissonAtlasBlock_physicalBox atom z y k hA Csep j small hd negative hv.1 hv.2
    have he : T.E3 = B.E3 := tightPoissonAtlasBlock_E3 atom z y k hA Csep j small hd negative
    rw [← he]
    exact E3_le_prefix_times_variation T hp.toOrderedBox (actualPrefixEnvelope T)
      (actualPrefixEnvelope_nonneg T) (actual_coeff5_le_prefixEnvelope T)
  · rw [if_neg hv]
    have hz : B.E3 = 0 := by
      by_cases ho : OrderedBox B
      · have hH : B.H < 1 := lt_of_not_ge (fun hH => hv ⟨ho, hH⟩)
        exact E3_zero_of_H_lt_one B hH
      · exact E3_zero_of_not_ordered B ho
    simp only [hz, norm_zero, le_refl]

def actualFamilyPrefixVariationCost {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) : ℝ :=
  ∑ i : SourceBlockIndex atom z y,
    actualTightAbelCost atom z y i.1.val hA Csep i.2.2.1 i.2.1.val i.2.1.property i.2.2.2 /
      (i.2.1.val : ℝ)

theorem norm_genuineTypedE3_le_actualPrefixVariationCost
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ) :
    ‖genuineTypedE3 atom z y hA Csep‖ ≤ actualFamilyPrefixVariationCost atom z y hA Csep := by
  unfold genuineTypedE3 actualFamilyPrefixVariationCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hd : (0 : ℝ) < i.2.1.val := by
    exact_mod_cast (genuineBlock atom z y hA Csep i).d_pos
  rw [norm_div]
  have hdn : ‖(i.2.1.val : ℂ)‖ = (i.2.1.val : ℝ) := by simp
  rw [hdn]
  change ‖(poissonAtlasBlock atom z y i.1.val hA Csep i.2.2.1
      i.2.1.val i.2.1.property i.2.2.2).E3‖ / (i.2.1.val : ℝ) ≤ _
  exact div_le_div_of_nonneg_right
    (norm_actual_E3_le_tightAbelCost atom z y i.1.val hA Csep i.2.2.1
      i.2.1.val i.2.1.property i.2.2.2) hd.le

/-- Actual original S3 source after its displayed nonclean/correction
terms is controlled by this explicit finite prefix/variation cost. -/
theorem actual_S3_clean_residual_norm_le_prefixVariationCost
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ) :
    ‖literalS3Normalized atom z y - genuineNoncleanE2 atom z y hA Csep -
      sourceCorrectionsNormalized atom z y‖ ≤ actualFamilyPrefixVariationCost atom z y hA Csep := by
  have he : literalS3Normalized atom z y - genuineNoncleanE2 atom z y hA Csep -
      sourceCorrectionsNormalized atom z y = genuineTypedE3 atom z y hA Csep := by
    rw [literalS3Normalized_eq_typed_nonclean_corrections hA z y Csep]
    ring
  rw [he]
  exact norm_genuineTypedE3_le_actualPrefixVariationCost atom z y hA Csep

end ImbalancedChen.Part3.OriginalActualAbelPrefixCost20261028
