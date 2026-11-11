import ImbalancedChen.Certificates.P2PairedSelectedRows
import ImbalancedChen.LogPrimeBoxIntegral
import Mathlib.Tactic.FinCases

/-!
SOURCE ONLY; UNCOMPILED. Endpoint adapter for the adopted 186-strip,
17572-row paired mask. The outer prime boxes use P1's literal Ico
convention; the inner triangular fibre remains a < w < z < Z.
The existing seven-wall nullness, genuine Fubini and checked row
enclosures are reused, with the original K/80 and K/4 weights.

Almost-everywhere identities below concern real product volume only.
They do not discard arithmetic boundary atoms or identify a historical
parent, a finite prime sum, or an E0/E1 saved-estimator licence.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedHalfOpenIntegral

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open P2AdoptedRows P2AdoptedUnion P2SemanticGainSetIntegral
open P2PairedRoundingLedger P2PairedSelectedRows

/-- P1's left-closed, right-open ownership on t,u, with the original
strict triangular z,w fibre and the original row cutoff. -/
def halfOpenSupport (r : Row) : Set Point := {x |
  (tLower (indices r).1 : ℝ) ≤ x 0 ∧
  x 0 < (tUpper (indices r).1 : ℝ) ∧
  (uLower (indices r).2 : ℝ) ≤ x 1 ∧
  x 1 < (uUpper (indices r).2 : ℝ) ∧
  (a : ℝ) < x 3 ∧ x 3 < x 2 ∧ x 2 < (cutoff r : ℝ)}

/-- An exact dictionary to P1's genuine half-open logarithmic prime box.
No endpoint rounding or coordinate permutation enters the dictionary. -/
theorem mem_halfOpenSupport_primeBox (r : Row) (x : Point) :
    x ∈ halfOpenSupport r ↔
      (![x 0, x 1] : Fin 2 → ℝ) ∈
        ImbalancedChen.logPrimeBox
          ![(tLower (indices r).1 : ℝ), (uLower (indices r).2 : ℝ)]
          ![(tUpper (indices r).1 : ℝ), (uUpper (indices r).2 : ℝ)] ∧
      (a : ℝ) < x 3 ∧ x 3 < x 2 ∧ x 2 < (cutoff r : ℝ) := by
  constructor
  · rintro ⟨htl, htr, hul, hur, haw, hwz, hzZ⟩
    refine ⟨ImbalancedChen.mem_logPrimeBox.mpr ?_, haw, hwz, hzZ⟩
    intro i
    fin_cases i
    · exact ⟨htl, htr⟩
    · exact ⟨hul, hur⟩
  · rintro ⟨hbox, haw, hwz, hzZ⟩
    have ht := ImbalancedChen.mem_logPrimeBox.mp hbox 0
    have hu := ImbalancedChen.mem_logPrimeBox.mp hbox 1
    exact ⟨ht.1, ht.2, hu.1, hu.2, haw, hwz, hzZ⟩

theorem halfOpenSupport_measurable (r : Row) :
    MeasurableSet (halfOpenSupport r) := by
  have h0 : MeasurableSet {x : Point | (tLower (indices r).1 : ℝ) ≤ x 0} :=
    (isClosed_le continuous_const (continuous_apply 0)).measurableSet
  have h1 : MeasurableSet {x : Point | x 0 < (tUpper (indices r).1 : ℝ)} :=
    (isOpen_lt (continuous_apply 0) continuous_const).measurableSet
  have h2 : MeasurableSet {x : Point | (uLower (indices r).2 : ℝ) ≤ x 1} :=
    (isClosed_le continuous_const (continuous_apply 1)).measurableSet
  have h3 : MeasurableSet {x : Point | x 1 < (uUpper (indices r).2 : ℝ)} :=
    (isOpen_lt (continuous_apply 1) continuous_const).measurableSet
  have h4 : MeasurableSet {x : Point | (a : ℝ) < x 3} :=
    (isOpen_lt continuous_const (continuous_apply 3)).measurableSet
  have h5 : MeasurableSet {x : Point | x 3 < x 2} :=
    (isOpen_lt (continuous_apply 3) (continuous_apply 2)).measurableSet
  have h6 : MeasurableSet {x : Point | x 2 < (cutoff r : ℝ)} :=
    (isOpen_lt (continuous_apply 2) continuous_const).measurableSet
  exact h0.inter (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter h6)))))

theorem support_subset_halfOpenSupport (r : Row) :
    support r ⊆ halfOpenSupport r := by
  rintro x ⟨h0, h1, h2, h3, h4, h5, h6⟩
  exact ⟨h0.le, h1, h2.le, h3, h4, h5, h6⟩

theorem halfOpenSupport_subset_closedSupport (r : Row) :
    halfOpenSupport r ⊆ P2AdoptedUnion.closedSupport r := by
  rintro x ⟨h0, h1, h2, h3, h4, h5, h6⟩
  exact ⟨h0, h1.le, h2, h3.le, h4.le, h5.le, h6.le⟩

/-- The original closed nested support supplier also applies at both
newly included outer lower endpoints; the strict inner fibre is unchanged. -/
theorem halfOpenSupport_closedNested (r : Row) {x : Point}
    (hx : x ∈ halfOpenSupport r) :
    P2PairedFibreBuchstabVariableLower.FullMask.closedSupport r
      (x 0) (x 1) (x 2) (x 3) := by
  rcases hx with ⟨htl, htr, hul, hur, haw, hwz, hzZ⟩
  exact ⟨⟨htl, htr.le⟩, ⟨hul, hur.le⟩,
    ⟨(haw.trans hwz).le, hzZ.le⟩, ⟨haw.le, hwz.le⟩⟩

theorem halfOpenSupport_buchstab_argument (r : Row) {x : Point}
    (hx : x ∈ halfOpenSupport r) :
    (7 / 3 : ℝ) ≤ (1 - x 0 - x 1 - x 2 - x 3) / x 2 :=
  P2PairedFibreBuchstabVariableLower.FullMask.closedSupport_argument r
    (halfOpenSupport_closedNested r hx)

/-- Reuse the proved null walls; no new boundary-measure premise. -/
theorem halfOpenSupport_ae_eq_support (r : Row) :
    halfOpenSupport r =ᵐ[volume] support r := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [Filter.eventuallyEq_set.1 (closedSupport_ae_eq_support r)] with x hx
  exact ⟨fun hh => hx.mp (halfOpenSupport_subset_closedSupport r hh),
    fun ho => support_subset_halfOpenSupport r ho⟩

/-- Exact ownership at the added lower walls, not merely a.e. disjointness.
Separation uses the existing actual mesh endpoint inequalities. -/
theorem halfOpenSupport_unique_owner {r q : Row} {x : Point}
    (hr : x ∈ halfOpenSupport r) (hq : x ∈ halfOpenSupport q) : r = q := by
  apply indices_injective
  apply Prod.ext
  · rcases lt_trichotomy (indices r).1 (indices q).1 with h | h | h
    · have hb : (tUpper (indices r).1 : ℝ) ≤ (tLower (indices q).1 : ℝ) :=
        Rat.cast_le.mpr (tUpper_le_tLower h)
      exact False.elim ((not_lt_of_ge (hb.trans hq.1)) hr.2.1)
    · exact h
    · have hb : (tUpper (indices q).1 : ℝ) ≤ (tLower (indices r).1 : ℝ) :=
        Rat.cast_le.mpr (tUpper_le_tLower h)
      exact False.elim ((not_lt_of_ge (hb.trans hr.1)) hq.2.1)
  · rcases lt_trichotomy (indices r).2 (indices q).2 with h | h | h
    · have hb : (uUpper (indices r).2 : ℝ) ≤ (uLower (indices q).2 : ℝ) :=
        Rat.cast_le.mpr (uUpper_le_uLower h)
      exact False.elim ((not_lt_of_ge (hb.trans hq.2.2.1)) hr.2.2.2.1)
    · exact h
    · have hb : (uUpper (indices q).2 : ℝ) ≤ (uLower (indices r).2 : ℝ) :=
        Rat.cast_le.mpr (uUpper_le_uLower h)
      exact False.elim ((not_lt_of_ge (hb.trans hr.2.2.1)) hq.2.2.2.1)

def halfOpenUnion (s : Finset Row) : Set Point := ⋃ r ∈ s, halfOpenSupport r

/-- The complete adopted mask, without truncation to a numerical prefix. -/
def halfOpenRegion : Set Point := halfOpenUnion Finset.univ

theorem halfOpenUnion_measurable (s : Finset Row) :
    MeasurableSet (halfOpenUnion s) :=
  MeasurableSet.iUnion (fun r =>
    MeasurableSet.iUnion (fun _ => halfOpenSupport_measurable r))

theorem halfOpenUnion_unique_owner (s : Finset Row) (x : Point) :
    x ∈ halfOpenUnion s ↔ ∃! r : Row, r ∈ s ∧ x ∈ halfOpenSupport r := by
  constructor
  · intro hx
    obtain ⟨r, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hr, hxr⟩ := Set.mem_iUnion.mp hx
    refine ⟨r, ⟨hr, hxr⟩, ?_⟩
    intro q hq
    exact halfOpenSupport_unique_owner hq.2 hxr
  · rintro ⟨r, hr, _⟩
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr.1, hr.2⟩⟩

/-- Every finite selection has exactly the same product-volume domain
as its original open selection, up to the already proved null walls. -/
theorem halfOpenUnion_ae_eq_rowUnion (s : Finset Row) :
    halfOpenUnion s =ᵐ[volume] rowUnion s := by
  have hall : ∀ᵐ x : Point ∂volume, ∀ r : Row,
      x ∈ halfOpenSupport r ↔ x ∈ support r :=
    MeasureTheory.ae_all_iff.2 (fun r =>
      Filter.eventuallyEq_set.1 (halfOpenSupport_ae_eq_support r))
  rw [Filter.eventuallyEq_set]
  filter_upwards [hall] with x hx
  simp only [halfOpenUnion, rowUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, hr, (hx r).mp hxr⟩
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, hr, (hx r).mpr hxr⟩

theorem halfOpenRegion_ae_eq_region :
    halfOpenRegion =ᵐ[volume] region := by
  have hu : rowUnion (Finset.univ : Finset Row) = region := by
    ext x
    simp [rowUnion, region]
  simpa only [halfOpenRegion, hu] using halfOpenUnion_ae_eq_rowUnion Finset.univ

/-- Endpoint transport applies to the real integrands themselves. -/
theorem halfOpenUnion_setIntegral_eq (s : Finset Row) (f : Point → ℝ) :
    (∫ x : Point in halfOpenUnion s, f x) =
      ∫ x : Point in rowUnion s, f x :=
  setIntegral_congr_set (halfOpenUnion_ae_eq_rowUnion s)

theorem halfOpenSupport_integrable_raw (r : Row) :
    IntegrableOn rawKernel (halfOpenSupport r) (volume : Measure Point) :=
  (integrableOn_support r).congr_set_ae (halfOpenSupport_ae_eq_support r)

theorem halfOpenUnion_integrable_semantic (s : Finset Row) :
    IntegrableOn semanticKernel (halfOpenUnion s) (volume : Measure Point) :=
  (integrableOn_semanticKernel_region.mono_set (rowUnion_subset_region s)).congr_set_ae
    (halfOpenUnion_ae_eq_rowUnion s)

theorem halfOpenRegion_integrable_raw :
    IntegrableOn rawKernel halfOpenRegion (volume : Measure Point) :=
  integrableOn_region.congr_set_ae halfOpenRegion_ae_eq_region

/-- Each half-open row is the original genuine local integral. -/
theorem halfOpenSupport_constant_integral (r : Row) :
    ((K : ℝ) / 80) * (∫ x : Point in halfOpenSupport r, rawKernel x) =
      gridIntegral (indices r) := by
  rw [setIntegral_congr_set (halfOpenSupport_ae_eq_support r)]
  exact P2PairedSupportFubini.support_setIntegral_eq_pairedLocalIntegral r

/-- Actual omega at the unchanged residual, with the original K/4
weight, agrees with the original literal fourfold semantic integral. -/
theorem halfOpenSupport_semantic_integral (r : Row) :
    (∫ x : Point in halfOpenSupport r, semanticKernel x) =
      P2PairedFibreBuchstabVariableLower.FullMask.rowGainIntegral r := by
  rw [setIntegral_congr_set (halfOpenSupport_ae_eq_support r)]
  exact support_semanticIntegral_eq_rowGainIntegral r

theorem halfOpenUnion_constant_eq_sum (s : Finset Row) :
    ((K : ℝ) / 80) * (∫ x : Point in halfOpenUnion s, rawKernel x) =
      ∑ r ∈ s, gridIntegral (indices r) := by
  rw [halfOpenUnion_setIntegral_eq, rowUnion, partial_setIntegral_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ =>
    P2PairedSupportFubini.support_setIntegral_eq_pairedLocalIntegral r)

/-- Finite selected bounds retain their original checked endpoints. -/
theorem halfOpenUnion_constant_bounds (s : Finset Row) :
    ((∑ r ∈ s, (makeCertificate r (approximation r)).lower : ℚ) : ℝ) ≤
      ((K : ℝ) / 80) * (∫ x : Point in halfOpenUnion s, rawKernel x) ∧
    ((K : ℝ) / 80) * (∫ x : Point in halfOpenUnion s, rawKernel x) ≤
      ((∑ r ∈ s, (makeCertificate r (approximation r)).upper : ℚ) : ℝ) := by
  rw [halfOpenUnion_constant_eq_sum]
  exact partial_actual_enclosure s

theorem halfOpenUnion_semantic_bounds (s : Finset Row) :
    lowerBudget s ≤ (∫ x : Point in halfOpenUnion s, semanticKernel x) ∧
      (∫ x : Point in halfOpenUnion s, semanticKernel x) ≤ 10 * upperBudget s := by
  simp only [halfOpenUnion_setIntegral_eq]
  exact selected_semantic_bounds s

theorem halfOpenRegion_constant_eq_unionIntegral :
    ((K : ℝ) / 80) * (∫ x : Point in halfOpenRegion, rawKernel x) = unionIntegral := by
  rw [setIntegral_congr_set halfOpenRegion_ae_eq_region]
  rfl

theorem halfOpenRegion_semantic_eq_unionSemanticIntegral :
    (∫ x : Point in halfOpenRegion, semanticKernel x) = unionSemanticIntegral :=
  setIntegral_congr_set halfOpenRegion_ae_eq_region

theorem halfOpenRegion_semantic_eq_fullSemanticGain :
    (∫ x : Point in halfOpenRegion, semanticKernel x) =
      P2PairedSemanticGainEnclosure.fullSemanticGain :=
  halfOpenRegion_semantic_eq_unionSemanticIntegral.trans
    unionSemanticIntegral_eq_fullSemanticGain

/-- Full-mask integral enclosure, keeping all 17572 adopted rows. -/
theorem halfOpenRegion_constant_bounds :
    lowerEndpoint ≤ ((K : ℝ) / 80) * (∫ x : Point in halfOpenRegion, rawKernel x) ∧
    ((K : ℝ) / 80) * (∫ x : Point in halfOpenRegion, rawKernel x) ≤ upperEndpoint := by
  rw [halfOpenRegion_constant_eq_unionIntegral]
  exact P2PairedSupportFubini.union_actual_enclosure

/-- Actual omega gain has its honest factor-ten upper side, not the
narrow constant-minorant upper endpoint. -/
theorem halfOpenRegion_semantic_bounds :
    lowerEndpoint ≤ (∫ x : Point in halfOpenRegion, semanticKernel x) ∧
      (∫ x : Point in halfOpenRegion, semanticKernel x) ≤ 10 * upperEndpoint := by
  rw [halfOpenRegion_semantic_eq_unionSemanticIntegral]
  exact actual_semantic_enclosure

theorem halfOpenRegion_rounding_error :
    roundingReserve ≤
        ((K : ℝ) / 80) * (∫ x : Point in halfOpenRegion, rawKernel x) - adoptedFloor ∧
      ((K : ℝ) / 80) * (∫ x : Point in halfOpenRegion, rawKernel x) - adoptedFloor ≤
        roundingReserve + enclosureWidth := by
  rw [halfOpenRegion_constant_eq_unionIntegral]
  exact union_rounding_error

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedHalfOpenIntegral
