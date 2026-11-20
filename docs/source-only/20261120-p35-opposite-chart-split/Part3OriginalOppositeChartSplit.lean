import ImbalancedChen.Part3OriginalOppositeExceptionalSplit

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Exact physical opposite-chart split with the original outer factors. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalOppositeChartSplit20261120
open Finset Set MeasureTheory Complex
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest actualCoeff)
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open ActualOppositeBesselTransform20261112
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalCommonPoissonLanes20261102
open OriginalTwoZSourceAssembly20261102 OriginalTwoZFourierAssembly20261102
open OriginalSignedTraceInput20261102 OriginalFullModulusSupport20261102
open OriginalFullModulusCuspInput20261102 OriginalFullModulusAssembly20261102
open OriginalNativeCuspFunctionals20261102 OriginalContinuousClassRemoval20261110
open OriginalPrescribedChartSpectrum20261112
  (rowSpectrum chartSpectrum full_chart_opposite_spectrum)
open OriginalExceptionalJNativeCompletion20261110 (exceptional)
open OriginalExceptionalChartIndex20261120
  (chartLevelEquiv chartSignedSlot signed_mode_eq_original_chart_sum)
open OriginalSignedExceptionalMode20261120 (signedExceptionalMode)
open OriginalOppositeExceptionalSplit20261120 (opposite_row_exceptional_split)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- The actual native cusp complement at one original chart level. -/
def oppositeRowComplement (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    (N : ℝ) (z : ↥(chartLevels D k upper)) : ℂ :=
  let q := ((chartLevelEquiv D k upper).symm z).val
  let Φ := spectralTest ell (chartY0 D k upper j N)
  ∑' i : {i : actualCuspBasisIndex q.val q.property // i ∉ exceptional q},
    (8*kTransform (basisOrder q.val q.property i.val) Φ) *
      (star (originalMFunctional J j ell q.val q.property i.val) *
        originalNFunctional D r k upper negativeM ell q.val q.property i.val)

/-- The original continuous density at that same level. -/
def oppositeRowContinuous (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    (N : ℝ) (z : ↥(chartLevels D k upper)) : ℂ :=
  let row : Row D k := ⟨z.val,chartLevels_subset D k upper z.property⟩
  let Φ := spectralTest ell (chartY0 D k upper j N)
  ∫ t : ℝ, continuousDensity Φ z.val t
    (fun a => M J j ell (fun n => nativeR a false n t))
    (fun a => source D r k row upper negativeM ell (fun n => nativeR a true n t))

/-- The original Fourier coefficient and physical outside scalar are
applied once to the whole complementary cuspidal chart. -/
def oppositeComplementMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell *
    (((M*Real.sqrt (fixedZ D upper):ℝ):ℂ) *
      ∑ z : ↥(chartLevels D k upper), oppositeRowComplement D r k upper negativeM J j ell N z)

/-- The same original outer factors applied once to the continuous chart. -/
def oppositeContinuousMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell *
    (((M*Real.sqrt (fixedZ D upper):ℝ):ℂ) *
      ∑ z : ↥(chartLevels D k upper), oppositeRowContinuous D r k upper negativeM J j ell N z)

/-- Exact one-chart return, including the existing exceptional mode,
the native cusp complement and the original continuous integral. -/
theorem opposite_chart_split (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (M : ℝ) {N : ℝ}
    (ell : D4 → ℤ) (hN : 0 < N) (ha : D.block.atom.residue ≠ 0)
    (hs : traceNegative D k negativeM = true) :
    actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell *
        fullChartMode D r k upper J j negativeM M N ell =
      signedExceptionalMode D r k upper negativeM J j M N ell +
        oppositeComplementMode D r k upper negativeM J j M N ell +
        oppositeContinuousMode D r k upper negativeM J j M N ell := by
  classical
  let E := fun z : ↥(chartLevels D k upper) =>
    ∑ i : ↥(exceptional ((chartLevelEquiv D k upper).symm z).val),
      chartSignedSlot D r k upper negativeM J j ell (chartY0 D k upper j N) z i
  let R := fun z : ↥(chartLevels D k upper) =>
    oppositeRowComplement D r k upper negativeM J j ell N z
  let C := fun z : ↥(chartLevels D k upper) =>
    oppositeRowContinuous D r k upper negativeM J j ell N z
  have hrows : (∑ z : ↥(chartLevels D k upper),
      rowSpectrum D r k ⟨z.val,chartLevels_subset D k upper z.property⟩
        upper negativeM J j ell N) = (∑ z, E z) + (∑ z, R z) + ∑ z, C z := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    simpa only [E,R,C,oppositeRowComplement,oppositeRowContinuous] using
      (opposite_row_exceptional_split D r k upper negativeM J j ell hN ha hs z)
  have hchart : chartSpectrum D r k upper negativeM J j M N ell =
      (((M*Real.sqrt (fixedZ D upper):ℝ):ℂ) *
        ∑ z : ↥(chartLevels D k upper),
          rowSpectrum D r k ⟨z.val,chartLevels_subset D k upper z.property⟩
            upper negativeM J j ell N) := by
    simp only [chartSpectrum,Finset.univ_eq_attach]
  rw [full_chart_opposite_spectrum D r k ha upper negativeM hs J j ell M hN,
    hchart,hrows,signed_mode_eq_original_chart_sum]
  simp only [oppositeComplementMode,oppositeContinuousMode,E,R,C]
  ring

end ImbalancedChen.Part3.OriginalOppositeChartSplit20261120
end
