import ImbalancedChen.Part3OriginalExceptionalChartIndex
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
The strict exceptional finite part and its exact complementary native
cuspidal sum in the original opposite-sign physical chart row. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalOppositeExceptionalSplit20261120
open Finset Set MeasureTheory Complex
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open ActualOppositeBesselTransform20261112
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalCommonPoissonLanes20261102
open OriginalTwoZSourceAssembly20261102 OriginalTwoZFourierAssembly20261102
open OriginalSignedTraceInput20261102 OriginalFullModulusSupport20261102
open OriginalFullModulusCuspInput20261102 OriginalFullModulusAssembly20261102
open OriginalNativeCuspFunctionals20261102 OriginalContinuousClassRemoval20261110
open OriginalPrescribedChartSpectrum20261112 (rowSpectrum row_spectrum_majorant)
open OriginalExceptionalJNativeCompletion20261110 (exceptional mem_exceptional)
open OriginalExceptionalChartIndex20261120 (chartLevelEquiv chartSignedSlot chart_slot_opposite)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- For an occupied level, the native cusp series in the actual opposite
row is exactly the already-indexed strict exceptional sum plus its
complement. The original continuous integral is carried unchanged. -/
theorem opposite_row_exceptional_split
    (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) {N : ℝ}
    (hN : 0 < N) (ha : D.block.atom.residue ≠ 0)
    (hs : traceNegative D k negativeM = true)
    (z : ↥(chartLevels D k upper)) :
    let q := ((chartLevelEquiv D k upper).symm z).val
    let row : Row D k := ⟨z.val, chartLevels_subset D k upper z.property⟩
    let Φ := spectralTest ell (chartY0 D k upper j N)
    let F := fun i : actualCuspBasisIndex q.val q.property =>
      (8*kTransform (basisOrder q.val q.property i) Φ) *
        (star (originalMFunctional J j ell q.val q.property i) *
          originalNFunctional D r k upper negativeM ell q.val q.property i)
    let G := fun t : ℝ => continuousDensity Φ z.val t
      (fun a => M J j ell (fun n => nativeR a false n t))
      (fun a => source D r k row upper negativeM ell (fun n => nativeR a true n t))
    rowSpectrum D r k row upper negativeM J j ell N =
      (∑ i : ↥(exceptional q), chartSignedSlot D r k upper negativeM J j ell
        (chartY0 D k upper j N) z i) +
      (∑' i : {i // i ∉ exceptional q}, F i.val) + ∫ t, G t := by
  classical
  let q := ((chartLevelEquiv D k upper).symm z).val
  let row : Row D k := ⟨z.val, chartLevels_subset D k upper z.property⟩
  let Φ := spectralTest ell (chartY0 D k upper j N)
  let F := fun i : actualCuspBasisIndex q.val q.property =>
    (8*kTransform (basisOrder q.val q.property i) Φ) *
      (star (originalMFunctional J j ell q.val q.property i) *
        originalNFunctional D r k upper negativeM ell q.val q.property i)
  let G := fun t : ℝ => continuousDensity Φ z.val t
    (fun a => M J j ell (fun n => nativeR a false n t))
    (fun a => source D r k row upper negativeM ell (fun n => nativeR a true n t))
  have hn : Summable (fun i => ‖F i‖) := by
    have h := (row_spectrum_majorant D r k row ha upper negativeM J j ell hN).1
    simpa only [F, Φ, q, row, chartLevelEquiv] using h
  have hsum : (∑ i : ↥(exceptional q), F i.val) +
      (∑' i : {i // i ∉ exceptional q}, F i.val) = ∑' i, F i := by
    simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
      (Summable.of_norm hn).sum_add_tsum_subtype_compl (exceptional q)
  have hfinite : (∑ i : ↥(exceptional q), F i.val) =
      ∑ i : ↥(exceptional q), chartSignedSlot D r k upper negativeM J j ell
        (chartY0 D k upper j N) z i := by
    apply Finset.sum_congr rfl
    intro i _
    symm
    simpa only [F, Φ, q] using
      (chart_slot_opposite D r k upper negativeM J j ell
        (chartY0 D k upper j N) z i hs)
  change (∑' i, F i) + ∫ t, G t = _
  rw [← hsum, hfinite]

/-- The complement contains exactly the native basis indices outside the
strict interval; the endpoint 1/4 belongs to this remainder. -/
theorem outside_exceptional_iff (q : ℕ+)
    (i : actualCuspBasisIndex q.val q.property) :
    i ∉ exceptional q ↔ ¬ (0 < actualCuspNativeEigenvalue q.val q.property i ∧
      actualCuspNativeEigenvalue q.val q.property i < 1/4) := by
  exact not_congr (mem_exceptional q i)

end ImbalancedChen.Part3.OriginalOppositeExceptionalSplit20261120
end
