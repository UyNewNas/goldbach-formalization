import ImbalancedChen.Part3OriginalMarkedHolomorphicSpectrum
import ImbalancedChen.Part3OriginalSixOppositeSpectrum
import Batteries.Tactic.OpenPrivate

/-! The full marked spectrum at every original chart. The scale
M sqrt(fixedZ), both source rows and the Poisson weight are retained. -/
namespace ImbalancedChen.Part3.OriginalPrescribedPositiveChart20261112
noncomputable section
open Complex
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest actualCoeff)
open OriginalPositiveScalarRemainder20261112 OriginalPrescribedPositiveTrace20261112 OriginalMarkedHolomorphicSpectrum20261112
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalPrimaryPacketRows20261102 OriginalCommonPoissonLanes20261102
open OriginalTwoZSourceAssembly20261102 OriginalTwoZFourierAssembly20261102
open OriginalSignedTraceInput20261102 OriginalFullModulusSupport20261102
open OriginalFullModulusCuspInput20261102 OriginalFullModulusAssembly20261102
open OriginalPositiveCompactPretrace20261112 (marking)
open private positive_moduli from ImbalancedChen.Part3OriginalPrescribedChartSpectrum

def positiveRow (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4→ℤ) (N : ℝ) : ℂ :=
  (∑' v : ℕ,markedWeight D r k z upper negativeM J j ell (chartY0 D k upper j N) v)+
    scalar D r k z upper negativeM J j ell (chartY0 D k upper j N)

theorem full_level_positive (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (ha : D.block.atom.residue≠0) (upper negativeM : Bool) (hs : traceNegative D k negativeM=false)
    (J j : ℕ) (ell : D4→ℤ) (M : ℝ) {N : ℝ} (hN : 0<N) (hz : z.val∈chartLevels D k upper) :
    (∑ n∈nCarrier D k z.val,∑ p∈commonMBlock J j,fullModulusRow D r k upper J j negativeM M N ell z.val n p)=
      ((M*Real.sqrt (fixedZ D upper):ℝ):ℂ)*positiveRow D r k z upper negativeM J j ell N := by
  have H := (original_prescribed_positive_trace D r k z upper negativeM J j ell ha hs
    (original_spectral_scale_pos D k upper j hN ha)).2.2.2
  have hol := (marked_holomorphic D r k z upper negativeM J j ell ha hs (original_spectral_scale_pos D k upper j hN ha)).2.tsum_eq
  rw [positiveRow,hol]
  let C : ℂ := ((M*Real.sqrt (fixedZ D upper):ℝ):ℂ)
  apply Eq.trans _ (congrArg (fun w => C*w) H)
  simp only [offDiagonal,marking,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro p _
  rw [fullModulusRow_eq_normalized_cusp_sum D r k upper J j negativeM M N ell hz,positive_moduli]
  dsimp only [C]; ring

def positiveChart (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4→ℤ) : ℂ :=
  ((M*Real.sqrt (fixedZ D upper):ℝ):ℂ)*∑ z∈(chartLevels D k upper).attach,
    positiveRow D r k ⟨z.val,chartLevels_subset D k upper z.property⟩ upper negativeM J j ell N

theorem full_chart_positive (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (ha : D.block.atom.residue≠0) (upper negativeM : Bool) (hs : traceNegative D k negativeM=false)
    (J j : ℕ) (ell : D4→ℤ) (M : ℝ) {N : ℝ} (hN : 0<N) :
    fullChartMode D r k upper J j negativeM M N ell=positiveChart D r k upper negativeM J j M N ell := by
  let A := chartLevels D k upper
  let F := fun z : ℕ => ∑ n∈nCarrier D k z,∑ p∈commonMBlock J j,fullModulusRow D r k upper J j negativeM M N ell z n p
  change (∑ z∈A,F z)=_
  rw [←Finset.sum_attach A F,positiveChart,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  exact full_level_positive D r k ⟨z.val,chartLevels_subset D k upper z.property⟩ ha upper negativeM hs J j ell M hN z.property

def positiveBlock (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (J j : ℕ) (negativeM : Bool) (M N : ℝ) (ell : D4→ℤ) : ℂ :=
  actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell*
    (positiveChart D r k false negativeM J j M N ell+positiveChart D r k true negativeM J j M N ell)

theorem full_block_positive (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (ha : D.block.atom.residue≠0) (J j : ℕ) (negativeM : Bool) (hs : traceNegative D k negativeM=false)
    (M : ℝ) {N : ℝ} (hN : 0<N) (ell : D4→ℤ) :
    fullBlockMode D r k J j negativeM M N ell=positiveBlock D r k J j negativeM M N ell := by
  rw [fullBlockMode,positiveBlock,full_chart_positive D r k ha false negativeM hs J j ell M hN,
    full_chart_positive D r k ha true negativeM hs J j ell M hN]

end
end ImbalancedChen.Part3.OriginalPrescribedPositiveChart20261112
