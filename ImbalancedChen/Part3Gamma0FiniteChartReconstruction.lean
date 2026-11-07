import ImbalancedChen.Part3Gamma0FiniteMeasureCarrier
import Mathlib.Order.Disjointed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal finite Gamma0 class charts admit a measurable disjoint
reconstruction on their height-truncated modular cells. Overlaps are
assigned once by `disjointed`, rather than counted as separate quotient
mass. The reconstruction and its squared-error budget are proved here.
No Rellich theorem, partition reconstruction, tail estimate, weak-domain
identification, or compact embedding is an input.

This leaf supplies the finite-chart assembly primitive only. Comparison
with the canonical quotient measure, smooth localized chart energy bounds,
and the identification of the finite physical cusp-zero graphs with all
actual cusps remain OPEN; this module asserts no global compact embedding.
-/

namespace ImbalancedChen.Part3.Gamma0FiniteChartReconstruction20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators ENNReal
open Gamma0FiniteMeasureCarrier20261024z
open ModularFundamentalFiniteMeasure20261024z

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

abbrev ChartIndex (N : ℕ) [NeZero N] := Fin (Fintype.card (gamma0Classes N))

def chartClass (N : ℕ) [NeZero N] (i : ChartIndex N) : gamma0Classes N :=
  (Fintype.equivFin (gamma0Classes N)).symm i

def chartMatrix (N : ℕ) [NeZero N] (i : ChartIndex N) : SL(2, ℤ) :=
  inverseClassRep N (chartClass N i)

def chartCoordinate (N : ℕ) [NeZero N] (i : ChartIndex N)
    (z : UpperHalfPlane) : UpperHalfPlane := (chartMatrix N i)⁻¹ • z

theorem chartCoordinate_continuous (N : ℕ) [NeZero N] (i : ChartIndex N) :
    Continuous (chartCoordinate N i) := by
  change Continuous (fun z : UpperHalfPlane =>
    (Matrix.SpecialLinearGroup.mapGL ℝ (chartMatrix N i)⁻¹) • z)
  exact continuous_const_smul _

def truncatedModularCell (Y : ℝ) : Set UpperHalfPlane :=
  modularFD ∩ {z | z.im ≤ Y}

theorem truncatedModularCell_measurable (Y : ℝ) :
    MeasurableSet (truncatedModularCell Y) :=
  modularFD_measurable.inter (isClosed_le UpperHalfPlane.continuous_im
    continuous_const).measurableSet

/-- The genuine inverse-class translate, expressed by its actual inverse
coordinate map so measurability needs no selected abstract chart map. -/
def rawChartCell (N : ℕ) [NeZero N] (Y : ℝ) (i : ChartIndex N) :
    Set UpperHalfPlane := chartCoordinate N i ⁻¹' truncatedModularCell Y

def core (N : ℕ) [NeZero N] (Y : ℝ) : Set UpperHalfPlane :=
  ⋃ i : ChartIndex N, rawChartCell N Y i

def chartPiece (N : ℕ) [NeZero N] (Y : ℝ) (i : ChartIndex N) :
    Set UpperHalfPlane := disjointed (rawChartCell N Y) i

theorem rawChartCell_measurable (N : ℕ) [NeZero N] (Y : ℝ) (i : ChartIndex N) :
    MeasurableSet (rawChartCell N Y i) :=
  (chartCoordinate_continuous N i).measurable (truncatedModularCell_measurable Y)

theorem chartPiece_measurable (N : ℕ) [NeZero N] (Y : ℝ) (i : ChartIndex N) :
    MeasurableSet (chartPiece N Y i) := by
  exact disjointedRec (fun _ _ ht => ht.diff (rawChartCell_measurable N Y _))
    (rawChartCell_measurable N Y i)

theorem chartPiece_subset (N : ℕ) [NeZero N] (Y : ℝ) (i : ChartIndex N) :
    chartPiece N Y i ⊆ rawChartCell N Y i := disjointed_subset _ _

theorem chartPieces_disjoint (N : ℕ) [NeZero N] (Y : ℝ) :
    Pairwise (fun i j : ChartIndex N => Disjoint (chartPiece N Y i) (chartPiece N Y j)) :=
  disjoint_disjointed _

theorem chartPieces_cover (N : ℕ) [NeZero N] (Y : ℝ) :
    (⋃ i : ChartIndex N, chartPiece N Y i) = core N Y := iUnion_disjointed

theorem core_measurable (N : ℕ) [NeZero N] (Y : ℝ) : MeasurableSet (core N Y) :=
  MeasurableSet.iUnion (rawChartCell_measurable N Y)

theorem core_subset_carrier (N : ℕ) [NeZero N] (Y : ℝ) :
    core N Y ⊆ gamma0Carrier N := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  apply mem_iUnion.mpr
  refine ⟨chartClass N i, ?_⟩
  rw [mem_smul_set_iff_inv_smul_mem]
  exact hi.1

/-- The same finite index is retained in the reconstruction. -/
theorem chartIndex_card (N : ℕ) [NeZero N] :
    Fintype.card (ChartIndex N) = (CongruenceSubgroup.Gamma0 N).index := by
  simpa only [ChartIndex, Fintype.card_fin] using gamma0Classes_card_eq_index N

def reconstruct (N : ℕ) [NeZero N] (Y : ℝ)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑ i : ChartIndex N, (chartPiece N Y i).indicator
    (fun w => v i (chartCoordinate N i w)) z

theorem reconstruct_on_piece (N : ℕ) [NeZero N] (Y : ℝ)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (i : ChartIndex N)
    {z : UpperHalfPlane} (hz : z ∈ chartPiece N Y i) :
    reconstruct N Y v z = v i (chartCoordinate N i z) := by
  classical
  unfold reconstruct
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hz _
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact Set.disjoint_left.mp (chartPieces_disjoint N Y hji) hj hz
  · simp

theorem reconstruct_outside_core (N : ℕ) [NeZero N] (Y : ℝ)
    (v : ChartIndex N → UpperHalfPlane → ℂ) {z : UpperHalfPlane}
    (hz : z ∉ core N Y) : reconstruct N Y v z = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hz (mem_iUnion.mpr ⟨i, chartPiece_subset N Y i hi⟩)

/-- Exact finite reconstruction, including all overlaps and the exterior.
The chart functions are the literal actual inverse-class pullbacks. -/
theorem reconstruct_actual_pullbacks (N : ℕ) [NeZero N] (Y : ℝ)
    (f : UpperHalfPlane → ℂ) :
    reconstruct N Y (fun i w => f (chartMatrix N i • w)) =
      (core N Y).indicator f := by
  classical
  funext z
  by_cases hz : z ∈ core N Y
  · obtain ⟨i, hi⟩ := mem_iUnion.mp ((chartPieces_cover N Y).symm ▸ hz)
    rw [reconstruct_on_piece N Y _ i hi, indicator_of_mem hz]
    simp only [chartCoordinate, smul_inv_smul]
  · rw [reconstruct_outside_core N Y _ hz, indicator_of_notMem hz]

/-- A finite error budget over the full actual chart cells. No smoothness
or measurability of f or v is needed for this nonnegative outer integral
bound: measurable disjoint cells suffice. Each overlap is charged once. -/
theorem reconstruction_square_error_budget (N : ℕ) [NeZero N] (Y : ℝ)
    (f : UpperHalfPlane → ℂ) (v : ChartIndex N → UpperHalfPlane → ℂ)
    (μ : Measure UpperHalfPlane) :
    (∫⁻ z in core N Y, ENNReal.ofReal (‖f z - reconstruct N Y v z‖ ^ 2) ∂μ) ≤
      ∑ i : ChartIndex N, ∫⁻ z in rawChartCell N Y i,
        ENNReal.ofReal (‖f z - v i (chartCoordinate N i z)‖ ^ 2) ∂μ := by
  rw [← chartPieces_cover N Y, lintegral_iUnion (chartPiece_measurable N Y)
    (chartPieces_disjoint N Y), tsum_fintype]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = ∫⁻ z in chartPiece N Y i,
        ENNReal.ofReal (‖f z - v i (chartCoordinate N i z)‖ ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (chartPiece_measurable N Y i)] with z hz
      rw [reconstruct_on_piece N Y v i hz]
    _ ≤ _ := lintegral_mono_set (chartPiece_subset N Y i)

end
end ImbalancedChen.Part3.Gamma0FiniteChartReconstruction20261026b
