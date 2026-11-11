import ImbalancedChen.Certificates.P2PairedRoundingLedger

/-!
SOURCE ONLY, UNCOMPILED. Actual finite-row deletion interface for the
adopted paired-v2 mask. Reuses the original row checker and genuine
set-integral Fubini bridge. No new quadrature or historical licence.

The upper bound is ten times the constant-minorant upper certificate:
the narrow certificate upper endpoint is never asserted for actual omega.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedSelectedRows

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open P2AdoptedRows P2AdoptedUnion P2SemanticGainSetIntegral
open P2PairedSemanticRestrictionError P2PairedRoundingLedger

def rowUnion (s : Finset Row) : Set Point := ⋃ r ∈ s, support r

def lowerBudget (s : Finset Row) : ℝ :=
  ∑ r ∈ s, ((makeCertificate r (approximation r)).lower : ℝ)

def upperBudget (s : Finset Row) : ℝ :=
  ∑ r ∈ s, ((makeCertificate r (approximation r)).upper : ℝ)

theorem rowUnion_measurable (s : Finset Row) : MeasurableSet (rowUnion s) := by
  exact (isOpen_iUnion (fun r => isOpen_iUnion (fun _ => support_isOpen r))).measurableSet

theorem rowUnion_subset_region (s : Finset Row) : rowUnion s ⊆ region := by
  intro x hx
  obtain ⟨r, hx⟩ := mem_iUnion.mp hx
  obtain ⟨_, hx⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨r, hx⟩

/-- Every omitted point has exactly a row outside the retained selection.
The original disjointness of actual grid supports pays the reverse direction. -/
theorem removed_rowUnion (s : Finset Row) : removed (rowUnion s) = rowUnion sᶜ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := mem_iUnion.mp hx.1
    have hn : r ∉ s := by
      intro hs
      exact hx.2 (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hs, hr⟩⟩)
    exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨Finset.mem_compl.mpr hn, hr⟩⟩
  · intro hx
    obtain ⟨r, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hr, hx⟩ := mem_iUnion.mp hx
    refine ⟨mem_iUnion.mpr ⟨r, hx⟩, ?_⟩
    intro hy
    obtain ⟨q, hy⟩ := mem_iUnion.mp hy
    obtain ⟨hq, hy⟩ := mem_iUnion.mp hy
    have hne : r ≠ q := by
      intro he
      subst q
      exact (Finset.mem_compl.mp hr) hq
    exact Set.disjoint_left.mp (supports_pairwise_disjoint hne) hx hy

theorem row_semantic_bounds (r : Row) :
    ((makeCertificate r (approximation r)).lower : ℝ) ≤
      (∫ x : Point in support r, semanticKernel x) ∧
    (∫ x : Point in support r, semanticKernel x) ≤
      10 * ((makeCertificate r (approximation r)).upper : ℝ) := by
  have hlocal : ((K : ℝ) / 80) * (∫ x : Point in support r, rawKernel x) =
      gridIntegral (indices r) :=
    P2PairedSupportFubini.support_setIntegral_eq_pairedLocalIntegral r
  have hlo := setIntegral_mono_on
    ((integrableOn_support r).const_mul ((K : ℝ) / 80))
    (integrableOn_semanticKernel_support r) (support_measurable r)
    (fun x hx => support_kernel_ge_certificate r hx)
  have hhi := setIntegral_mono_on
    (integrableOn_semanticKernel_support r)
    (((integrableOn_support r).const_mul ((K : ℝ) / 80)).const_mul 10)
    (support_measurable r)
    (fun x hx => semanticKernel_le_ten_certificate (mem_iUnion.mpr ⟨r, hx⟩))
  simp only [integral_const_mul, hlocal] at hlo hhi
  exact ⟨(row_actual_enclosure r).1.trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_left (row_actual_enclosure r).2 (by norm_num))⟩

/-- Genuine actual semantic integral bounds for every finite adopted
selection, with proved integrability and disjoint coverage inherited. -/
theorem selected_semantic_bounds (s : Finset Row) :
    lowerBudget s ≤ retainedGain (rowUnion s) ∧
      retainedGain (rowUnion s) ≤ 10 * upperBudget s := by
  have he : retainedGain (rowUnion s) =
      ∑ r ∈ s, ∫ x : Point in support r, semanticKernel x :=
    partialSemanticIntegral_eq_sum s
  rw [he]
  constructor
  · exact Finset.sum_le_sum (fun r _ => (row_semantic_bounds r).1)
  · unfold upperBudget
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => (row_semantic_bounds r).2)

theorem lostGain_eq_complement (s : Finset Row) :
    lostGain (rowUnion s) = retainedGain (rowUnion sᶜ) := by
  unfold lostGain retainedGain
  rw [removed_rowUnion]

/-- Certificate-local loss control, not a uniform full-box volume bound.
All discarded rows are included in the complement exactly once. -/
theorem omitted_rows_loss_le (s : Finset Row) :
    lostGain (rowUnion s) ≤ 10 * upperBudget sᶜ := by
  rw [lostGain_eq_complement]
  exact (selected_semantic_bounds sᶜ).2

theorem retained_lower_from_omitted_rows (s : Finset Row) :
    lowerEndpoint - 10 * upperBudget sᶜ ≤ retainedGain (rowUnion s) := by
  have he := full_sub_retained_eq_lost (rowUnion_measurable s) (rowUnion_subset_region s)
  have hl : lowerEndpoint ≤ unionSemanticIntegral := unionSemanticIntegral_lower
  have hu := omitted_rows_loss_le s
  linarith

/-- Concrete sufficient test for preserving the adopted rounded floor.
The finite omitted-row budget remains an honest input to discharge. -/
theorem retained_floor_of_omitted_budget (s : Finset Row)
    (hb : 10 * upperBudget sᶜ ≤ roundingReserve) :
    adoptedFloor ≤ retainedGain (rowUnion s) := by
  have hr := endpoint_rounding_reserve
  have hl := retained_lower_from_omitted_rows s
  linarith

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedSelectedRows
