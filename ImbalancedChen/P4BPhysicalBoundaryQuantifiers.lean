import ImbalancedChen.P4BSmoothPhysicalMassReserve
import ImbalancedChen.P4BSourceMassPrecision

/-!
# Uniform small-width closure for the actual physical boundary

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The four arithmetic wall estimates are imported, not assumed again.
This module counts distinct actual products in their union and closes the
width quantifiers uniformly: one threshold works for every smaller positive
width. It also retains the original coefficient log(1/b) in the normalized
smooth mass. The upper wall is physical, m < exp(width) N.
No sifted-count estimate or prime-product distribution assertion is made.
-/

namespace ImbalancedChen.P4B

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary

/-- Distinct products of jointly supported boundary tuples. The image
removes orientation multiplicities and overlaps between walls. -/
def physicalBoundaryProducts (width b : ℝ) (N : ℕ) (T : ℝ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin 4)).biUnion
    (fun i => physicalSupportedStrip width b N T i)).image labelledProduct

/-- The exact product count is paid by the four genuine tuple strips.
No ambient square of a prime carrier occurs. -/
theorem physicalBoundaryProducts_card_le_strip_sum (width b : ℝ) (N : ℕ) (T : ℝ) :
    ((physicalBoundaryProducts width b N T).card : ℝ) ≤
      ∑ i : Fin 4, ((physicalSupportedStrip width b N T i).card : ℝ) := by
  have hfinite : (physicalBoundaryProducts width b N T).card ≤
      ∑ i : Fin 4, (physicalSupportedStrip width b N T i).card := by
    exact Finset.card_image_le.trans Finset.card_biUnion_le
  exact_mod_cast hfinite

/-- One selected width and one threshold control the COUNT for every
smaller positive width, before any smoothing or density insertion. -/
theorem exists_uniform_physical_boundary_count_reserve
    {b kappa : ℝ} (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (eta widthMax : ℝ) (heta : 0 < eta) (hwidthMax : 0 < widthMax) :
    ∃ width0 : ℝ, 0 < width0 ∧ width0 ≤ widthMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ width : ℝ, 0 < width → width ≤ width0 →
        ∀ N : ℕ, N0 ≤ N → Even N →
          ((physicalBoundaryProducts width b N
            (manuscriptHalfProductCutoff kappa N)).card : ℝ) ≤
              eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨width0, hwidth0, hmax, N0, hN0, hsum⟩ :=
    exists_physical_supported_strip_sum_reserve
      hbLower hbUpper hkappa hkappaOne eta widthMax heta hwidthMax
  refine ⟨width0, hwidth0, hmax, N0, hN0, ?_⟩
  intro width _hwidth hle N hN hEven
  calc
    _ ≤ ∑ i : Fin 4, ((physicalSupportedStrip width b N
          (manuscriptHalfProductCutoff kappa N) i).card : ℝ) :=
      physicalBoundaryProducts_card_le_strip_sum _ _ _ _
    _ ≤ ∑ i : Fin 4, ((physicalSupportedStrip width0 b N
          (manuscriptHalfProductCutoff kappa N) i).card : ℝ) :=
      Finset.sum_le_sum (fun i _ => physicalSupportedStrip_cast_card_mono hle i)
    _ ≤ _ := hsum N hN hEven

/-- The exact manuscript coefficient survives smoothing uniformly over
all sufficiently small positive widths, with N quantified only afterwards.
The threshold is independent of the smaller width. -/
theorem exists_uniform_smooth_physical_mass_precision
    {b kappa : ℝ} (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (epsilon widthMax : ℝ) (hepsilon : 0 < epsilon) (hwidthMax : 0 < widthMax) :
    ∃ width0 : ℝ, 0 < width0 ∧ width0 ≤ widthMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ width : ℝ, 0 < width → width ≤ width0 →
        ∀ N : ℕ, N0 ≤ N → Even N →
          |(∑ t ∈ labelledPrimeTuples 2 N,
              smoothPhysicalPairOuterRamp b N
                (manuscriptHalfProductCutoff kappa N) width t) /
              ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b)| < epsilon := by
  obtain ⟨width0, hwidth0, hmax, Ns, hNs, hstrips⟩ :=
    exists_physical_supported_strip_sum_reserve hbLower hbUpper hkappa hkappaOne
      (epsilon / 2) widthMax (half_pos hepsilon) hwidthMax
  obtain ⟨Nm, hmass⟩ := Filter.eventually_atTop.mp
    (p4b_eventually_manuscriptSource_absolute_mass_error
      hbLower hbUpper hkappa (epsilon / 2) (half_pos hepsilon))
  let N0 := max Ns Nm
  refine ⟨width0, hwidth0, hmax, N0, hNs.trans (le_max_left _ _), ?_⟩
  intro width hwidth hle N hN hEven
  have hNsN : Ns ≤ N := (le_max_left Ns Nm).trans hN
  have hNmN : Nm ≤ N := (le_max_right Ns Nm).trans hN
  obtain ⟨hscale, herror⟩ := hmass N hNmN
  have hN2 : 2 ≤ N := hNs.trans hNsN
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hT : 0 < manuscriptHalfProductCutoff kappa N :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans hN1) _)
  have hsum : (∑ i : Fin 4, ((physicalSupportedStrip width b N
      (manuscriptHalfProductCutoff kappa N) i).card : ℝ)) ≤
        (epsilon / 2) * ((N : ℝ) / Real.log (N : ℝ)) := by
    exact (Finset.sum_le_sum (fun i _ =>
      physicalSupportedStrip_cast_card_mono hle i)).trans (hstrips N hNsN hEven)
  have hupper :=
    (sum_smoothPhysicalPairOuterRamp_le_source_card_add_supported_strip_cards
      (b := b) hN1 hT hwidth).trans (add_le_add_left hsum _)
  have hlower : ((realHalfProductSource b N
      (manuscriptHalfProductCutoff kappa N)).card : ℝ) ≤
      ∑ t ∈ labelledPrimeTuples 2 N, smoothPhysicalPairOuterRamp b N
        (manuscriptHalfProductCutoff kappa N) width t := by
    rw [← sum_actual_labelled_W_eq_source_card]
    exact Finset.sum_le_sum (fun t ht =>
      actual_W_le_smoothPhysicalPairOuterRamp hN1 hT hwidth ht)
  have herrors := abs_lt.mp herror
  apply abs_lt.mpr
  constructor
  · have hlo : (Real.log (1 / b) - epsilon) *
        ((N : ℝ) / Real.log (N : ℝ)) <
        ∑ t ∈ labelledPrimeTuples 2 N, smoothPhysicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) width t := by
      nlinarith only [herrors.1, hlower, mul_pos hepsilon hscale]
    have hh := (lt_div_iff₀ hscale).mpr hlo
    linarith only [hh]
  · have hhi : (∑ t ∈ labelledPrimeTuples 2 N,
        smoothPhysicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) width t) <
        (Real.log (1 / b) + epsilon) * ((N : ℝ) / Real.log (N : ℝ)) := by
      nlinarith only [herrors.2, hupper]
    have hh := (div_lt_iff₀ hscale).mpr hhi
    linarith only [hh]

end
end ImbalancedChen.P4B
