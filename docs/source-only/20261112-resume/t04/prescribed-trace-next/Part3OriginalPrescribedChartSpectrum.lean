import ImbalancedChen.Part3OriginalPrescribedOppositeTrace
import ImbalancedChen.Part3OriginalPrescribedSpectralConvergence
import ImbalancedChen.Part3OriginalFullModulusCuspInput

/-! The exact normalized trace at every occupied level of one original
chart. The physical outside scalar is restored after summing both
markings. The total mass of each original marked spectrum is finite. -/
namespace ImbalancedChen.Part3.OriginalPrescribedChartSpectrum20261112

noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest actualCoeff)
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalPrimaryPacketRows20261102 OriginalCommonPoissonLanes20261102
open OriginalTwoZSourceAssembly20261102 OriginalTwoZFourierAssembly20261102
open OriginalSignedTraceInput20261102 OriginalFullModulusSupport20261102
open OriginalFullModulusCuspInput20261102 OriginalFullModulusAssembly20261102
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open OriginalNativeCuspFunctionals20261102 OriginalContinuousClassRemoval20261110
open ActualOppositeBesselTransform20261112 OriginalOppositeMarkedKuznetsov20261112
open OriginalPrescribedOppositeTrace20261112 OriginalPrescribedSpectralConvergence20261112

def rowSpectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (N : ℝ) : ℂ :=
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let hz := NeZero.pos z.val
  let Φ := spectralTest ell (chartY0 D k upper j N)
  (∑' i : actualCuspBasisIndex z.val hz,(8*kTransform (basisOrder z.val hz i) Φ)*
    (star (originalMFunctional J j ell z.val hz i)*originalNFunctional D r k upper negativeM ell z.val hz i))+
    ∫ t : ℝ, continuousDensity Φ z.val t
      (fun a => M J j ell (fun h => nativeR a false h t))
      (fun a => source D r k z upper negativeM ell (fun h => nativeR a true h t))

theorem row_spectrum_majorant (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue≠0) (upper negativeM : Bool) (J j : ℕ)
    (ell : D4 → ℤ) {N : ℝ} (hN : 0<N) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let h := NeZero.pos z.val
    let Φ := spectralTest ell (chartY0 D k upper j N)
    let F := fun i : actualCuspBasisIndex z.val h => (8*kTransform (basisOrder z.val h i) Φ)*
      (star (originalMFunctional J j ell z.val h i)*originalNFunctional D r k upper negativeM ell z.val h i)
    let G := fun t => continuousDensity Φ z.val t
      (fun a => M J j ell (fun n => nativeR a false n t))
      (fun a => source D r k z upper negativeM ell (fun n => nativeR a true n t))
    Summable (fun i => ‖F i‖) ∧ Integrable (fun t => ‖G t‖) ∧
      ‖rowSpectrum D r k z upper negativeM J j ell N‖≤(∑' i,‖F i‖)+∫ t,‖G t‖ := by
  have H := original_prescribed_spectral_convergence D r k z ha upper negativeM J j ell
    (original_spectral_scale_pos D k upper j hN ha)
  exact ⟨H.2.1,H.1.norm,(norm_add_le _ _).trans (add_le_add (norm_tsum_le_tsum_norm H.2.1) (norm_integral_le_integral_norm _))⟩

private theorem positive_moduli (D : OriginalData) (k : BlockKey) (upper : Bool) (j : ℕ)
    (negativeM : Bool) (N : ℝ) (ell : D4 → ℤ) (z n p : ℕ) :
    (∑' c : ℕ,bareCuspTerm D k upper j negativeM N ell z n p c)=
      ∑' d : ℕ+,modulusTerm (spectralTest ell (chartY0 D k upper j N)) z p (traceIndex D k negativeM z n) d := by
  let B := bareCuspTerm D k upper j negativeM N ell z n p
  have zero : B 0=0 := by simp [B,bareCuspTerm]
  change (∑' c : ℕ,B c)=_
  rw [← tsum_pnat_eq_tsum_of_eq_zero zero]
  apply tsum_congr
  intro d
  by_cases e : z.Coprime (d:ℕ)
  · simp only [B,bareCuspTerm,dif_pos (show 0<(d:ℕ) ∧ (d:ℕ).Coprime z from ⟨d.property,e.symm⟩),
      modulusTerm,dif_pos e]
  · have no : ¬(0<(d:ℕ) ∧ (d:ℕ).Coprime z) := fun h => e h.2.symm
    simp only [B,bareCuspTerm,dif_neg no,modulusTerm,dif_neg e]

theorem full_level_row (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (ha : D.block.atom.residue≠0) (upper negativeM : Bool) (hs : traceNegative D k negativeM=true)
    (J j : ℕ) (ell : D4 → ℤ) (M : ℝ) {N : ℝ} (hN : 0<N) (hz : z.val∈chartLevels D k upper) :
    (∑ n∈nCarrier D k z.val,∑ p∈commonMBlock J j,
      fullModulusRow D r k upper J j negativeM M N ell z.val n p)=
        ((M*Real.sqrt (fixedZ D upper):ℝ):ℂ)*rowSpectrum D r k z upper negativeM J j ell N := by
  have hY := original_spectral_scale_pos D k upper j hN ha
  have H := (original_prescribed_opposite_trace D r k z ha upper negativeM hs J j ell hY).2.2.2
  let C : ℂ := ((M*Real.sqrt (fixedZ D upper):ℝ):ℂ)
  apply Eq.trans _ (congrArg (fun w : ℂ => C*w) H)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro p _
  rw [fullModulusRow_eq_normalized_cusp_sum D r k upper J j negativeM M N ell hz,positive_moduli]
  dsimp only [C]
  ring

def chartSpectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  ((M*Real.sqrt (fixedZ D upper):ℝ):ℂ)*∑ z∈(chartLevels D k upper).attach,
    rowSpectrum D r k ⟨z.val,chartLevels_subset D k upper z.property⟩ upper negativeM J j ell N

theorem full_chart_opposite_spectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (ha : D.block.atom.residue≠0) (upper negativeM : Bool) (hs : traceNegative D k negativeM=true)
    (J j : ℕ) (ell : D4 → ℤ) (M : ℝ) {N : ℝ} (hN : 0<N) :
    fullChartMode D r k upper J j negativeM M N ell=chartSpectrum D r k upper negativeM J j M N ell := by
  let A := chartLevels D k upper
  let F := fun z : ℕ => ∑ n∈nCarrier D k z,∑ p∈commonMBlock J j,fullModulusRow D r k upper J j negativeM M N ell z n p
  change (∑ z∈A,F z)=_
  rw [← Finset.sum_attach A F,chartSpectrum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact full_level_row D r k ⟨z.val,chartLevels_subset D k upper z.property⟩ ha upper negativeM hs J j ell M hN z.property

def oppositeBlockSpectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (J j : ℕ) (negativeM : Bool) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell*
    (chartSpectrum D r k false negativeM J j M N ell+chartSpectrum D r k true negativeM J j M N ell)

theorem full_block_opposite_spectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (ha : D.block.atom.residue≠0) (J j : ℕ) (negativeM : Bool) (hs : traceNegative D k negativeM=true)
    (M : ℝ) {N : ℝ} (hN : 0<N) (ell : D4 → ℤ) :
    fullBlockMode D r k J j negativeM M N ell=oppositeBlockSpectrum D r k J j negativeM M N ell := by
  rw [fullBlockMode,oppositeBlockSpectrum,full_chart_opposite_spectrum D r k ha false negativeM hs J j ell M hN,
    full_chart_opposite_spectrum D r k ha true negativeM hs J j ell M hN]

end
end ImbalancedChen.Part3.OriginalPrescribedChartSpectrum20261112
