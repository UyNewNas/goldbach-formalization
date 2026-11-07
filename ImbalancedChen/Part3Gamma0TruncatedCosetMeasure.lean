import ImbalancedChen.Part3Gamma0QuotientChartReconstruction
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The EXISTING actual finite-chart core and quotientCore are identified
with the inverse-coset translates of the literal height-truncated standard
modular cell. Their a.e. disjointness is inherited from the proved actual
modular fundamental-cell uniqueness/null-boundary theorem. Restriction
of the ORIGINAL quotient carrier measure to quotientCore is proved equal
to the pushforward of canonical hyperbolic volume on the actual core.
There is no prescribed quotient integral identity or tiling hypothesis.
The height boundary is retained; no cusp classification or spectral
measure normalization is claimed.
-/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane Pointwise BigOperators
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0FiniteCarrierExactMeasure20261024zz
open ImbalancedChen.Part3.Gamma0FiniteChartReconstruction20261026b
open ImbalancedChen.Part3.Gamma0QuotientChartReconstruction20261026b
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a

namespace ImbalancedChen.Part3.Gamma0TruncatedCosetMeasure20261026b

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

theorem rawChartCell_eq_translate (N : ℕ) [NeZero N] (T : ℝ) (i : ChartIndex N) :
    rawChartCell N T i = chartMatrix N i • truncatedModularCell T := by
  ext z
  simp only [rawChartCell, chartCoordinate, mem_preimage, mem_smul_set_iff_inv_smul_mem]

/-- The actual truncated carrier is the genuine finite inverse-coset
tiling, using the exact same representatives as the quotient construction. -/
theorem core_eq_iUnion_truncated_cosets (N : ℕ) [NeZero N] (T : ℝ) :
    core N T = ⋃ q : gamma0Classes N, inverseClassRep N q • truncatedModularCell T := by
  ext z
  constructor
  · rintro ⟨i, hi⟩
    refine mem_iUnion.mpr ⟨chartClass N i, ?_⟩
    rw [rawChartCell_eq_translate] at hi
    exact hi
  · rintro ⟨q, hq⟩
    let i : ChartIndex N := Fintype.equivFin (gamma0Classes N) q
    have hi : chartClass N i = q := (Fintype.equivFin (gamma0Classes N)).symm_apply_apply q
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [rawChartCell_eq_translate]
    simpa only [chartMatrix, hi] using hq

theorem truncated_coset_subset_full (N : ℕ) [NeZero N] (T : ℝ) (q : gamma0Classes N) :
    inverseClassRep N q • truncatedModularCell T ⊆ inverseClassRep N q • modularFD := by
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, hw.1, rfl⟩

theorem truncated_coset_measurable (N : ℕ) [NeZero N] (T : ℝ) (q : gamma0Classes N) :
    MeasurableSet (inverseClassRep N q • truncatedModularCell T) := by
  change MeasurableSet ((Matrix.SpecialLinearGroup.mapGL ℝ (inverseClassRep N q)) •
    truncatedModularCell T)
  exact (truncatedModularCell_measurable T).const_smul _

/-- Actual fundamental-cell uniqueness supplies the overlap control.
No arbitrary disjointness condition is among the premises. -/
theorem truncated_cosets_aeDisjoint (N : ℕ) [NeZero N] (T : ℝ) :
    Pairwise (AEDisjoint (volume : Measure UpperHalfPlane) on
      fun q : gamma0Classes N => inverseClassRep N q • truncatedModularCell T) := by
  intro q r hqr
  exact (distinct_coset_cells_aeDisjoint N hqr).mono
    (truncated_coset_subset_full N T q) (truncated_coset_subset_full N T r)

/-- Equality of the actual restricted volume with the finite sum of its
genuine coset-cell restrictions. Central +/-I is already counted once. -/
theorem restrict_core_eq_sum_truncated_cells (N : ℕ) [NeZero N] (T : ℝ) :
    (volume : Measure UpperHalfPlane).restrict (core N T) =
      ∑ q : gamma0Classes N,
        (volume : Measure UpperHalfPlane).restrict (inverseClassRep N q • truncatedModularCell T) := by
  rw [core_eq_iUnion_truncated_cosets,
    Measure.restrict_iUnion_ae (truncated_cosets_aeDisjoint N T)
      (fun q => (truncated_coset_measurable N T q).nullMeasurableSet), Measure.sum_fintype]

theorem quotientCore_preimage_inter_reduced (N : ℕ) [NeZero N] (T : ℝ) :
    orbitProjection N ⁻¹' quotientCore N T ∩ reducedCarrier N = core N T ∩ reducedCarrier N := by
  ext z
  by_cases hz : z ∈ reducedCarrier N
  · have h := quotientCore_projection_iff N T (⟨z, hz⟩ : reducedCarrier N)
    change (orbitProjection N z ∈ quotientCore N T ∧ z ∈ reducedCarrier N) ↔
      (z ∈ core N T ∧ z ∈ reducedCarrier N)
    simpa only [reducedProjection, hz, and_true] using h
  · simp only [mem_inter_iff, hz, and_false]

/-- Removing only the already-proved translated modular null boundary
does not change the actual truncated carrier volume. -/
theorem core_inter_reduced_ae_eq (N : ℕ) [NeZero N] (T : ℝ) :
    core N T ∩ reducedCarrier N =ᵐ[(volume : Measure UpperHalfPlane)] core N T := by
  filter_upwards [reducedCarrier_ae_eq_carrier N] with z hz
  apply propext
  change (z ∈ core N T ∧ z ∈ reducedCarrier N) ↔ z ∈ core N T
  rw [hz]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, core_subset_carrier N T h⟩

/-- TRUE restricted quotient volume, derived from the actual reduced
section and its original canonical spatial pushforward. -/
theorem quotientCore_restrict_measure (N : ℕ) [NeZero N] (T : ℝ) :
    (carrierPushforward N).restrict (quotientCore N T) = cellPushforward N (core N T) := by
  rw [← reducedCarrier_pushforward_eq N]
  unfold cellPushforward
  rw [Measure.restrict_map (orbitProjection_measurable N) (quotientCore_measurable N T),
    Measure.restrict_restrict ((orbitProjection_measurable N) (quotientCore_measurable N T)),
    quotientCore_preimage_inter_reduced,
    Measure.restrict_congr_set (core_inter_reduced_ae_eq N T)]

/-- A nonnegative quotient observable now has an exact true truncated
carrier formula. This is a conclusion from the measure identity above. -/
theorem lintegral_quotientCore_eq_core (N : ℕ) [NeZero N] (T : ℝ)
    (F : Gamma0OrbitSpace N → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q in quotientCore N T, F q ∂carrierPushforward N) =
      ∫⁻ z in core N T, F (orbitProjection N z) := by
  rw [quotientCore_restrict_measure]
  exact lintegral_cellPushforward N (core N T) F hF

end ImbalancedChen.Part3.Gamma0TruncatedCosetMeasure20261026b
