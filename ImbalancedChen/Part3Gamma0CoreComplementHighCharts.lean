import ImbalancedChen.Part3Gamma0QuotientCoreExhaustion
import ImbalancedChen.Part3Gamma0ChartCoordinateErrorBudget

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The complement of the literal quotient core is covered, on its actual
reduced carrier, by the finite ORIGINAL inverse-class modular high cells.
This gives a weighted nonnegative integral bound for arbitrary measurable
quotient observables, with actual matrix coordinate changes and coefficient
one for each class. No uniform analytic cusp tail bound is an input.
Overlapping or repeated cusp frames are retained in the finite sum.
-/

namespace ImbalancedChen.Part3.Gamma0CoreComplementHighCharts20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators ENNReal
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0FiniteChartReconstruction20261026b
open Gamma0QuotientChartReconstruction20261026b
open Gamma0ChartCoordinateErrorBudget20261026b
open Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

def modularHighCell (Y : ℝ) : Set UpperHalfPlane :=
  ModularFundamentalFiniteMeasure20261024z.modularFD ∩ {z | Y < z.im}

def rawHighChartCell (N : ℕ) [NeZero N] (Y : ℝ) (i : ChartIndex N) : Set UpperHalfPlane :=
  chartCoordinate N i ⁻¹' modularHighCell Y

theorem modularHighCell_measurable (Y : ℝ) : MeasurableSet (modularHighCell Y) :=
  ModularFundamentalFiniteMeasure20261024z.modularFD_measurable.inter
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet

theorem rawHighChartCell_measurable (N : ℕ) [NeZero N] (Y : ℝ) (i : ChartIndex N) :
    MeasurableSet (rawHighChartCell N Y i) :=
  (chartCoordinate_continuous N i).measurable (modularHighCell_measurable Y)

/-- The frame orientation is the ORIGINAL inverseClassRep, derived from
membership in the original finite carrier, not a right-coset substitute. -/
theorem exists_high_chart_of_reduced_core_complement (N : ℕ) [NeZero N] (Y : ℝ)
    (z : reducedCarrier N) (hz : reducedProjection N z ∉ quotientCore N Y) :
    ∃ i : ChartIndex N, (z : UpperHalfPlane) ∈ rawHighChartCell N Y i := by
  obtain ⟨q, hq⟩ := mem_iUnion.mp z.property.1
  rw [mem_smul_set_iff_inv_smul_mem] at hq
  let i : ChartIndex N := Fintype.equivFin (gamma0Classes N) q
  have hi : chartClass N i = q := (Fintype.equivFin (gamma0Classes N)).symm_apply_apply q
  have hfd : chartCoordinate N i z ∈
      ModularFundamentalFiniteMeasure20261024z.modularFD := by
    simpa only [chartCoordinate, chartMatrix, hi] using hq
  refine ⟨i, hfd, ?_⟩
  by_contra hnot
  have hlow : (chartCoordinate N i z).im ≤ Y := le_of_not_gt hnot
  apply hz
  apply (quotientCore_projection_iff N Y z).mpr
  exact mem_iUnion.mpr ⟨i, hfd, hlow⟩

theorem reduced_complement_subset_high_charts (N : ℕ) [NeZero N] (Y : ℝ) :
    (orbitProjection N ⁻¹' (quotientCore N Y)ᶜ) ∩ reducedCarrier N ⊆
      ⋃ i : ChartIndex N, rawHighChartCell N Y i := by
  intro z hz
  obtain ⟨i, hi⟩ := exists_high_chart_of_reduced_core_complement N Y ⟨z,hz.2⟩ hz.1
  exact mem_iUnion.mpr ⟨i, hi⟩

theorem high_chart_lintegral_change_variables (N : ℕ) [NeZero N] (Y : ℝ)
    (i : ChartIndex N) (W : Gamma0OrbitSpace N → ℝ≥0∞) :
    (∫⁻ z in rawHighChartCell N Y i, W (orbitProjection N z)) =
      ∫⁻ w in modularHighCell Y, W (orbitProjection N (chartMatrix N i • w)) := by
  have h := (chartCoordinate_measurePreserving N i).setLIntegral_comp_preimage_emb
    (chartCoordinate_measurableEmbedding N i)
    (fun w => W (orbitProjection N (chartMatrix N i • w))) (modularHighCell Y)
  simpa only [rawHighChartCell, chartCoordinate, smul_inv_smul] using h

/-- Weighted tail domination in the actual finite modular charts. The
observable is arbitrary nonnegative measurable data, not just the constant
one used in earlier total-cusp MASS formulas. -/
theorem quotient_complement_lintegral_le_high_charts (N : ℕ) [NeZero N] (Y : ℝ)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ q in (quotientCore N Y)ᶜ, W q ∂carrierPushforward N) ≤
      ∑ i : ChartIndex N, ∫⁻ w in modularHighCell Y,
        W (orbitProjection N (chartMatrix N i • w)) := by
  have hm := (orbitProjection_measurable N) (quotientCore_measurable N Y).compl
  calc
    _ = ∫⁻ z in reducedCarrier N,
        ((quotientCore N Y)ᶜ).indicator W (orbitProjection N z) := by
      rw [← lintegral_indicator (quotientCore_measurable N Y).compl]
      exact lintegral_reducedCarrier N _ (hW.indicator (quotientCore_measurable N Y).compl)
    _ = ∫⁻ z in (orbitProjection N ⁻¹' (quotientCore N Y)ᶜ) ∩ reducedCarrier N,
        W (orbitProjection N z) := by
      change (∫⁻ z in reducedCarrier N,
        (orbitProjection N ⁻¹' (quotientCore N Y)ᶜ).indicator
          (fun z => W (orbitProjection N z)) z) = _
      rw [lintegral_indicator hm, Measure.restrict_restrict hm]
    _ ≤ ∫⁻ z in ⋃ i : ChartIndex N, rawHighChartCell N Y i,
        W (orbitProjection N z) :=
      lintegral_mono_set (reduced_complement_subset_high_charts N Y)
    _ ≤ ∑ i : ChartIndex N, ∫⁻ z in rawHighChartCell N Y i,
        W (orbitProjection N z) := by
      simpa only [tsum_fintype] using lintegral_iUnion_le
        (rawHighChartCell N Y) (fun z => W (orbitProjection N z))
    _ = _ := Finset.sum_congr rfl (fun i _ => high_chart_lintegral_change_variables N Y i W)

end
end ImbalancedChen.Part3.Gamma0CoreComplementHighCharts20261026b
