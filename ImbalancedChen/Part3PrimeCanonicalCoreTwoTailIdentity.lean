import ImbalancedChen.Part3PrimeUnequalCuspCoreSaturation
import ImbalancedChen.Part3Gamma0QuotientConullTransport

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL reduced quotientCore equals the full compact carrier image
intersected with the original reduced-section range. Thus the two-tail
identity for quotientCore is CANONICALLY ALMOST EVERYWHERE, retaining the
explicit exceptional range complement instead of deleting boundary orbits
pointwise. Restrictions use the original canonical quotient measure. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane MatrixGroups Pointwise
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0FiniteChartReconstruction20261026b
open ImbalancedChen.Part3.Gamma0QuotientChartReconstruction20261026b
open ImbalancedChen.Part3.Gamma0TruncatedCosetMeasure20261026b
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.ActualModularCutoffCompactSupport20261025a
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeUnequalCuspCoreSaturation20261026b

namespace ImbalancedChen.Part3.PrimeCanonicalCoreTwoTailIdentity20261026b

theorem core_eq_truncatedGammaCarrier (N : ℕ) [NeZero N] (T : ℝ) :
    core N T = truncatedGammaCarrier N T := by
  rw [core_eq_iUnion_truncated_cosets]
  rfl

/-- Exact boundary bookkeeping for the ORIGINAL canonical quotientCore.
Actual open-to-closed carrier uniqueness, rather than a new chosen
quotient section, proves the reverse inclusion. -/
theorem quotientCore_eq_full_inter_reduced_range (N : ℕ) [NeZero N] (T : ℝ) :
    quotientCore N T = quotientTruncatedCarrier N T ∩ range (reducedProjection N) := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨(z : UpperHalfPlane), ?_, rfl⟩, ⟨z, rfl⟩⟩
    rwa [← core_eq_truncatedGammaCarrier]
  · rintro ⟨⟨w, hw, hwq⟩, ⟨z, hzq⟩⟩
    have hwcore : w ∈ core N T := by rwa [core_eq_truncatedGammaCarrier]
    have he : orbitProjection N (z : UpperHalfPlane) = orbitProjection N w :=
      hzq.trans hwq.symm
    have hzw : (z : UpperHalfPlane) = w :=
      (orbitProjection_eq_iff_open_closed N (reducedCarrier_subset_open N z.property)
        (core_subset_carrier N T hwcore)).mp he
    refine ⟨z, ?_, hzq⟩
    rw [hzw]
    exact hwcore

theorem quotientCore_eq_unequal_inter_reduced_range (p : ℕ) [NeZero p]
    (hp : p.Prime) (T : ℝ) (hT : (p : ℝ) ≤ T) :
    quotientCore p T = unequalCuspTruncation p hp T ∩ range (reducedProjection p) := by
  rw [quotientCore_eq_full_inter_reduced_range,
    full_truncated_carrier_eq_unequal_truncation p hp T hT]

/-- This equality is a.e. for the ORIGINAL canonical quotient measure;
the exact pointwise theorem above still exhibits the missing boundary range. -/
theorem quotientCore_ae_eq_unequal_truncation (p : ℕ) [NeZero p]
    (hp : p.Prime) (T : ℝ) (hT : (p : ℝ) ≤ T) :
    quotientCore p T =ᵐ[carrierPushforward p] unequalCuspTruncation p hp T := by
  rw [quotientCore_eq_unequal_inter_reduced_range p hp T hT]
  filter_upwards [reducedProjection_range_ae p] with q hq
  simp only [mem_inter_iff, hq, and_true]

theorem quotientCore_compl_ae_eq_two_tails (p : ℕ) [NeZero p]
    (hp : p.Prime) (T : ℝ) (hT : (p : ℝ) ≤ T) :
    (quotientCore p T)ᶜ =ᵐ[carrierPushforward p]
      infinityHighNeighborhood p T ∪ zeroHighNeighborhood p hp (T / (p : ℝ)) := by
  filter_upwards [quotientCore_ae_eq_unequal_truncation p hp T hT] with q hq
  simp only [mem_compl_iff, hq, unequalCuspTruncation, not_not]

/-- Honest canonical restriction identity; 02782's actual core tiling and
the original conull section justify every measure used here. -/
theorem quotientCore_restrict_eq_unequal_truncation (p : ℕ) [NeZero p]
    (hp : p.Prime) (T : ℝ) (hT : (p : ℝ) ≤ T) :
    (carrierPushforward p).restrict (quotientCore p T) =
      (carrierPushforward p).restrict (unequalCuspTruncation p hp T) :=
  Measure.restrict_congr_set (quotientCore_ae_eq_unequal_truncation p hp T hT)

end ImbalancedChen.Part3.PrimeCanonicalCoreTwoTailIdentity20261026b
