import ImbalancedChen.P5U6OriginalRationalIntegralCertificates
import ImbalancedChen.P5U6OriginalPairedMaskNativeHarmonic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual adopted17572-row retained U6 rational integral certificates.
Only STATIC subfamilies of the actual original rows are used. A rational
disjointness test supplies retained inner cells. A rational containment
test removes wholly deleted cells from the retained outer staircase.
All source rows keep their Ico walls and are transposed exactly once from
(t,u) to U6(u,t). No arbitrary mask limit, supplied cover or numerical pass.
-/

namespace ImbalancedChen.P5U6OriginalRetainedRationalCertificates

noncomputable section

open Set MeasureTheory Classical
open scoped BigOperators
open P5U6OriginalRationalBoxBounds P5U6OriginalRationalIntegralCertificates
open P5U6AdoptedH248BindingSourceOnly P5U6RetainedAdoptedIntegralSourceOnly
open P5U6OriginalPairedMaskNativeHarmonicSourceOnly
open P5Z.U1011OriginalPairedFixedMaskHarmonic (outerUnion e0Rows e1Rows)
open Certificates.PairedV2

abbrev ActualRow := FullMask.Row

def rowULo (r : ActualRow) : ℚ := uLower (FullMask.indices r).2
def rowUHi (r : ActualRow) : ℚ := uUpper (FullMask.indices r).2
def rowTLo (r : ActualRow) : ℚ := tLower (FullMask.indices r).1
def rowTHi (r : ActualRow) : ℚ := tUpper (FullMask.indices r).1

def Separated (b : Box) (r : ActualRow) : Prop :=
  b.uHi ≤ rowULo r ∨ rowUHi r ≤ b.uLo ∨
    b.tHi ≤ rowTLo r ∨ rowTHi r ≤ b.tLo
def Contained (b : Box) (r : ActualRow) : Prop :=
  rowULo r ≤ b.uLo ∧ b.uHi ≤ rowUHi r ∧
    rowTLo r ≤ b.tLo ∧ b.tHi ≤ rowTHi r

instance (b : Box) (r : ActualRow) : Decidable (Separated b r) := by
  unfold Separated
  infer_instance
instance (b : Box) (r : ActualRow) : Decidable (Contained b r) := by
  unfold Contained
  infer_instance

theorem row_dictionary (r : ActualRow) (x : Fin 2 → ℝ) :
    (x 1, x 0) ∈ FullMask.P1E0E1.pairCell r ↔
      (rowULo r : ℝ) ≤ x 0 ∧ x 0 < (rowUHi r : ℝ) ∧
        (rowTLo r : ℝ) ≤ x 1 ∧ x 1 < (rowTHi r : ℝ) := by
  simp only [FullMask.P1E0E1.pairCell, mem_setOf_eq, rowULo, rowUHi, rowTLo, rowTHi]
  tauto

theorem actual_mask_dictionary (S : Finset ActualRow) (x : Fin 2 → ℝ) :
    x ∈ ascendingPointMask S ↔
      ∃ r ∈ S, (x 1, x 0) ∈ FullMask.P1E0E1.pairCell r := by
  simp only [ascendingPointMask, mem_setOf_eq, outerUnion, mem_iUnion]

theorem actual_mask_measurable (S : Finset ActualRow) :
    MeasurableSet (ascendingPointMask S) := by
  have hrow (r : ActualRow) : MeasurableSet (FullMask.P1E0E1.pairCell r) :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_const)))
  have houter : MeasurableSet (outerUnion S) :=
    Finset.measurableSet_biUnion S (fun r _ => hrow r)
  exact houter.preimage ((measurable_pi_apply 1).prodMk (measurable_pi_apply 0))

/-- Weak rational separation is correct because the source cells and
the generated cells BOTH have strict upper walls. -/
theorem separated_cell_avoids_row (n : ℕ) (j : Index n) (r : ActualRow)
    (hsep : Separated (gridBox n j) r) {x : Fin 2 → ℝ} (hx : x ∈ cell n j) :
    (x 1, x 0) ∉ FullMask.P1E0E1.pairCell r := by
  intro hr
  have hrow := (row_dictionary r x).1 hr
  have hcell := mem_logPrimeBox.mp hx
  rcases hsep with h | h | h | h
  · have hh : ((gridBox n j).uHi : ℝ) ≤ rowULo r := by exact_mod_cast h
    exact (not_lt_of_ge hrow.1) ((hcell 0).2.trans_le hh)
  · have hh : (rowUHi r : ℝ) ≤ (gridBox n j).uLo := by exact_mod_cast h
    exact (not_lt_of_ge (hh.trans (hcell 0).1)) hrow.2.1
  · have hh : ((gridBox n j).tHi : ℝ) ≤ rowTLo r := by exact_mod_cast h
    exact (not_lt_of_ge hrow.2.2.1) ((hcell 1).2.trans_le hh)
  · have hh : (rowTHi r : ℝ) ≤ (gridBox n j).tLo := by exact_mod_cast h
    exact (not_lt_of_ge (hh.trans (hcell 1).1)) hrow.2.2.2

theorem contained_cell_deleted (n : ℕ) (j : Index n) (r : ActualRow)
    (hcon : Contained (gridBox n j) r) {x : Fin 2 → ℝ} (hx : x ∈ cell n j) :
    (x 1, x 0) ∈ FullMask.P1E0E1.pairCell r := by
  have hcell := mem_logPrimeBox.mp hx
  have h0 : (rowULo r : ℝ) ≤ (gridBox n j).uLo := by exact_mod_cast hcon.1
  have h1 : ((gridBox n j).uHi : ℝ) ≤ rowUHi r := by exact_mod_cast hcon.2.1
  have h2 : (rowTLo r : ℝ) ≤ (gridBox n j).tLo := by exact_mod_cast hcon.2.2.1
  have h3 : ((gridBox n j).tHi : ℝ) ≤ rowTHi r := by exact_mod_cast hcon.2.2.2
  exact (row_dictionary r x).2 ⟨h0.trans (hcell 0).1,
    (hcell 0).2.trans_le h1, h2.trans (hcell 1).1, (hcell 1).2.trans_le h3⟩

def retainedInner (S : Finset ActualRow) (n : ℕ) : Finset (Index n) :=
  (inner n).filter (fun j => ∀ r ∈ S, Separated (gridBox n j) r)
def retainedOuter (S : Finset ActualRow) (n : ℕ) : Finset (Index n) :=
  (outer n).filter (fun j => ¬ ∃ r ∈ S, Contained (gridBox n j) r)
def retainedDomain (S : Finset ActualRow) : Set (Fin 2 → ℝ) :=
  currentChenUpsilon6LogDomain 0 \ ascendingPointMask S

theorem retainedDomain_measurable (S : Finset ActualRow) :
    MeasurableSet (retainedDomain S) := domain_measurable.diff (actual_mask_measurable S)

theorem retained_inner_cell_subset (S : Finset ActualRow) (n : ℕ)
    {j : Index n} (hj : j ∈ retainedInner S n) : cell n j ⊆ retainedDomain S := by
  intro x hx
  have hh := Finset.mem_filter.mp hj
  refine ⟨inner_cell_subset_domain n hh.1 hx, ?_⟩
  intro hm
  obtain ⟨r, hr, hxr⟩ := (actual_mask_dictionary S x).1 hm
  exact separated_cell_avoids_row n j r (hh.2 r hr) hx hxr

/-- A retained point forbids every row-containment certificate for its
actual grid owner; this proves a genuine retained outer cover. -/
theorem retained_outer_cover (S : Finset ActualRow) (n : ℕ) {x : Fin 2 → ℝ}
    (hx : x ∈ retainedDomain S) : ∃ j ∈ retainedOuter S n, x ∈ cell n j := by
  obtain ⟨j, hj, hxj⟩ := domain_outer_cover n hx.1
  refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩, hxj⟩
  rintro ⟨r, hr, hcon⟩
  exact hx.2 ((actual_mask_dictionary S x).2
    ⟨r, hr, contained_cell_deleted n j r hcon hxj⟩)

theorem retained_kernel_integrable (S : Finset ActualRow) :
    IntegrableOn adoptedKernel (retainedDomain S) :=
  (integrableOn_adoptedEnhancedKernel (by norm_num : (0 : ℝ) ≤ 0)).mono_set
    sdiff_subset

theorem retained_indicator_integrable (S : Finset ActualRow) :
    Integrable ((retainedDomain S).indicator adoptedKernel) :=
  (retained_kernel_integrable S).integrable_indicator (retainedDomain_measurable S)

theorem retained_indicator_nonneg (S : Finset ActualRow) (x : Fin 2 → ℝ) :
    0 ≤ (retainedDomain S).indicator adoptedKernel x := by
  by_cases hx : x ∈ retainedDomain S
  · simpa only [indicator_of_mem hx] using adoptedKernel_nonneg (by norm_num) hx.1
  · simp only [indicator_of_notMem hx, le_refl]

def retainedIntegral (S : Finset ActualRow) : ℝ :=
  retainedEstimatorIntegral (fun x => x ∈ ascendingPointMask S) 0

theorem retainedIntegral_eq_domain (S : Finset ActualRow) :
    retainedIntegral S = ∫ x in retainedDomain S, adoptedKernel x := rfl

def retainedRationalLower (S : Finset ActualRow) (n precision : ℕ) : ℚ :=
  ∑ j ∈ retainedInner S n, densityLower n precision j * area n j
def retainedRationalUpper (S : Finset ActualRow) (n precision : ℕ) : ℚ :=
  ∑ j ∈ retainedOuter S n, densityUpper n precision j * area n j

theorem retainedRationalLower_le (S : Finset ActualRow) (n precision : ℕ) :
    (retainedRationalLower S n precision : ℝ) ≤ retainedIntegral S := by
  have hf : Integrable (fun x => ∑ j ∈ retainedInner S n, minorant n precision j x) :=
    integrable_finsetSum _ (fun j _ => cell_constant_integrable n j _)
  have hpoint (x : Fin 2 → ℝ) : (∑ j ∈ retainedInner S n, minorant n precision j x) ≤
      (retainedDomain S).indicator adoptedKernel x := by
    by_cases hex : ∃ j ∈ retainedInner S n, x ∈ cell n j
    · obtain ⟨j, hj, hxj⟩ := hex
      have hD := retained_inner_cell_subset S n hj hxj
      have heq : (∑ k ∈ retainedInner S n, minorant n precision k x) =
          minorant n precision j x := by
        apply Finset.sum_eq_single j
        · intro k hk hkj
          exact indicator_of_notMem (fun hxk => hkj (cell_unique hxk hxj)) _
        · intro hnot
          exact (hnot hj).elim
      rw [heq, minorant, indicator_of_mem hxj, indicator_of_mem hD]
      exact (kernel_cell_bounds n precision j hxj hD.1).1
    · have hz : (∑ j ∈ retainedInner S n, minorant n precision j x) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact indicator_of_notMem (fun hxj => hex ⟨j, hj, hxj⟩) _
      rw [hz]
      exact retained_indicator_nonneg S x
  calc
    (retainedRationalLower S n precision : ℝ) =
        ∑ j ∈ retainedInner S n, ((densityLower n precision j * area n j : ℚ) : ℝ) := by
      simp [retainedRationalLower]
    _ = ∑ j ∈ retainedInner S n, ∫ x, minorant n precision j x := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_cell_constant n j _).symm
    _ = ∫ x, ∑ j ∈ retainedInner S n, minorant n precision j x :=
      (integral_finsetSum _ (fun j _ => cell_constant_integrable n j _)).symm
    _ ≤ ∫ x, (retainedDomain S).indicator adoptedKernel x :=
      integral_mono hf (retained_indicator_integrable S) hpoint
    _ = retainedIntegral S := integral_indicator (retainedDomain_measurable S)

theorem retainedIntegral_le_rationalUpper (S : Finset ActualRow) (n precision : ℕ) :
    retainedIntegral S ≤ (retainedRationalUpper S n precision : ℝ) := by
  have hg : Integrable (fun x => ∑ j ∈ retainedOuter S n, majorant n precision j x) :=
    integrable_finsetSum _ (fun j _ => cell_constant_integrable n j _)
  have hpoint (x : Fin 2 → ℝ) : (retainedDomain S).indicator adoptedKernel x ≤
      ∑ j ∈ retainedOuter S n, majorant n precision j x := by
    by_cases hx : x ∈ retainedDomain S
    · obtain ⟨j, hj, hxj⟩ := retained_outer_cover S n hx
      rw [indicator_of_mem hx]
      calc
        adoptedKernel x ≤ (densityUpper n precision j : ℝ) :=
          (kernel_cell_bounds n precision j hxj hx.1).2
        _ = majorant n precision j x := (indicator_of_mem hxj _).symm
        _ ≤ _ := Finset.single_le_sum (fun k _ => majorant_nonneg n precision k x) hj
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun j _ => majorant_nonneg n precision j x)
  calc
    retainedIntegral S = ∫ x, (retainedDomain S).indicator adoptedKernel x :=
      (integral_indicator (retainedDomain_measurable S)).symm
    _ ≤ ∫ x, ∑ j ∈ retainedOuter S n, majorant n precision j x :=
      integral_mono (retained_indicator_integrable S) hg hpoint
    _ = ∑ j ∈ retainedOuter S n, ∫ x, majorant n precision j x :=
      integral_finsetSum _ (fun j _ => cell_constant_integrable n j _)
    _ = ∑ j ∈ retainedOuter S n, ((densityUpper n precision j * area n j : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_cell_constant n j _
    _ = (retainedRationalUpper S n precision : ℝ) := by simp [retainedRationalUpper]

theorem actual_adopted_retained_enclosure (nL pL nU pU : ℕ) :
    (retainedRationalLower Finset.univ nL pL : ℝ) ≤ retainedIntegral Finset.univ ∧
      retainedIntegral Finset.univ ≤ (retainedRationalUpper Finset.univ nU pU : ℝ) :=
  ⟨retainedRationalLower_le _ _ _, retainedIntegral_le_rationalUpper _ _ _⟩
theorem actual_e0_retained_enclosure (nL pL nU pU : ℕ) :
    (retainedRationalLower e0Rows nL pL : ℝ) ≤ retainedIntegral e0Rows ∧
      retainedIntegral e0Rows ≤ (retainedRationalUpper e0Rows nU pU : ℝ) :=
  ⟨retainedRationalLower_le _ _ _, retainedIntegral_le_rationalUpper _ _ _⟩
theorem actual_e1_retained_enclosure (nL pL nU pU : ℕ) :
    (retainedRationalLower e1Rows nL pL : ℝ) ≤ retainedIntegral e1Rows ∧
      retainedIntegral e1Rows ≤ (retainedRationalUpper e1Rows nU pU : ℝ) :=
  ⟨retainedRationalLower_le _ _ _, retainedIntegral_le_rationalUpper _ _ _⟩

end

end ImbalancedChen.P5U6OriginalRetainedRationalCertificates
