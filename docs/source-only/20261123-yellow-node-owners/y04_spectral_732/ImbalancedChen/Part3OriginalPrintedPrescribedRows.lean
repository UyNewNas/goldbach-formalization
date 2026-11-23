import ImbalancedChen.Part3OriginalPrintedContinuousTrace
import ImbalancedChen.Part3OriginalBothSignsSixSpectrum
import ImbalancedChen.Part3PrintedHolomorphicRegularNorm
import Batteries.Tactic.OpenPrivate

/-! Coefficient normalization inside the prescribed physical trace. Both signs
use the same marked arithmetic finite rows. The opposite trace carries no
Petersson sum. The external Fourier mode stays outside all spectral sums. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPrintedPrescribedRows20261123

open Complex Finset MeasureTheory Matrix
open scoped BigOperators MatrixGroups Classical
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest actualCoeff)
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalPrimaryPacketRows20261102 OriginalCommonPoissonLanes20261102
open OriginalTwoZSourceAssembly20261102 OriginalTwoZFourierAssembly20261102
open OriginalSignedTraceInput20261102 OriginalFullModulusAssembly20261102 OriginalFullModulusSupport20261102
open OriginalNativeCuspFunctionals20261102 ActualCuspBasisWhittakerCoefficients20261102
open ActualFullCuspEigenbasis20261026b ActualCuspDenominatorClasses20261110
open ActualContinuousClassFourier20261110 ActualContinuousPoincarePairing20261110 (originalFrame)
open OriginalContinuousClassRemoval20261110 OriginalContinuousCuspGram20261110
open ActualOppositeBesselTransform20261112 OriginalOppositeMarkedKuznetsov20261112
open ActualPositiveNativeDiagonal20261112 ActualPrescribedPositiveJ20261112
open OriginalMarkedPacketLimits20261112 OriginalPositiveScalarRemainder20261112
open OriginalMarkedHolomorphicSpectrum20261112 OriginalPrescribedPositiveChart20261112
open OriginalPrescribedChartSpectrum20261112 OriginalOccupiedTraceSigns20261112
open OriginalSixOppositeSpectrum20261112 OriginalBothSignsSixSpectrum20261112
open Gamma0ActualCuspsSourceOnly (cuspOneMatrix)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicPeterssonSpace20261112 (Forms BasisIndex formsBasis)
open OriginalHolomorphicCuspFrames20261110 (frameR sieveCoeff_eq_scaled_R)
open ActualPositiveHolomorphicWeights20261112 (holWeight)
open PrintedHolomorphicRegularNorm20261123 (printedCoeff)
open private scale scale_sq from ImbalancedChen.Part3PrintedHolomorphicRegularNorm
open GeometricCriticalEisenstein20261123 (printedR)
open OriginalPrintedContinuousTrace20261123 (original_printed_trace_product)

section Row
variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
local instance : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
local notation "Z" => z.val
local notation "idx" => traceIndex D k negativeM Z
local notation "mRow" => M J j ell
local notation "nRow" => source D r k z upper negativeM ell

def eProduct (t : ℝ) : ℂ :=
  ∑ a : Parameters Z, star (mRow (fun n => printedR a false n t)) *
    nRow (fun n => printedR a true n t) / (Real.pi : ℂ)

private theorem eProduct_native (ha : D.block.atom.residue ≠ 0) (t : ℝ) :
    eProduct D r k z upper negativeM J j ell t =
      (4/(Real.cosh (Real.pi*t) : ℂ))*cMark D r k z upper negativeM J j ell t := by
  have h := original_printed_trace_product D r k z ha upper negativeM J j ell t
  rw [original_projected_product] at h
  exact h

private theorem pos_line (ha : D.block.atom.residue ≠ 0) (Φ : ℝ → ℂ) (t : ℝ) :
    (positiveWeight Φ t/(Real.cosh (Real.pi*t):ℂ))*cMark D r k z upper negativeM J j ell t =
      (positiveWeight Φ t/4)*eProduct D r k z upper negativeM J j ell t := by
  rw [eProduct_native D r k z upper negativeM J j ell ha]
  ring

private theorem neg_line (ha : D.block.atom.residue ≠ 0) (Φ : ℝ → ℂ) (t : ℝ) :
    continuousDensity Φ Z t (fun a => mRow (fun n => nativeR a false n t))
      (fun a => nRow (fun n => nativeR a true n t)) =
        (oppositeWeight Φ t/4)*eProduct D r k z upper negativeM J j ell t := by
  rw [eProduct_native D r k z upper negativeM J j ell ha, cMark, nativeProduct,
    ← Finset.sum_div, continuousDensity]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (Real.cosh (Real.pi*t):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  field_simp [hπ,hc] <;> ring

def mProduct (i : actualCuspBasisIndex Z (NeZero.pos Z)) : ℂ :=
  ∑ n ∈ nCarrier D k Z, ∑ p ∈ commonMBlock J j,
    (commonPoissonCompleted J j (ell 1)).weight p * traceBeta D r k upper negativeM ell Z n *
      (star (basisRhoK Z (NeZero.pos Z) i (1 : SL(2,ℤ)) (p:ℤ)) *
        basisRhoK Z (NeZero.pos Z) i cuspOneMatrix (idx n))

private theorem mProduct_native (ha : D.block.atom.residue ≠ 0)
    (i : actualCuspBasisIndex Z (NeZero.pos Z)) :
    dMark D r k z upper negativeM J j ell i = mProduct D r k z upper negativeM J j ell i/4 := by
  unfold dMark
  rw [← original_native_row_product D r k upper negativeM J j ell Z (NeZero.pos Z) i,
    mProduct, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  rw [original_native_coefficient_product D k negativeM J j Z (NeZero.pos Z) ha i hn hp]
  ring

private theorem hRow {q : ℕ} [NeZero q] (v : ℕ) (one : Bool) (S : Finset ℕ)
    (w : ℕ → ℂ) (idx : ℕ → ℤ) (hi : ∀ j ∈ S, 0 < (idx j).natAbs) (f : Forms q (v+1)) :
    markedRow S w idx (fun n => printedCoeff q v one f n.natAbs) =
      (scale v : ℂ)*markedRow S w idx
        (fun n => frameR q (NeZero.pos q) (v+1) f (originalFrame one) n.natAbs) := by
  rw [markedRow, markedRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [printedCoeff,sieveCoeff_eq_scaled_R q (NeZero.pos q) (v+1) f (originalFrame one) (hi n hn)]
  simp only [scale, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

def hProduct (v : ℕ) (i : BasisIndex Z (v+1)) : ℂ :=
  star (mRow (fun n => printedCoeff Z v false (formsBasis Z (v+1) i) n.natAbs)) *
    nRow (fun n => printedCoeff Z v true (formsBasis Z (v+1) i) n.natAbs) /
      (2*(Real.pi : ℂ))

private theorem hProduct_native (ha : D.block.atom.residue ≠ 0) (Y : ℝ)
    (v : ℕ) (i : BasisIndex Z (v+1)) :
    markedCoordinate D r k z upper negativeM J j ell Y v i =
      (holWeight v (spectralTest ell Y)/2)*hProduct D r k z upper negativeM J j ell v i := by
  let f := formsBasis Z (v+1) i
  have hM : mRow (fun n => printedCoeff Z v false f n.natAbs) =
      (scale v : ℂ) * mRow (fun n => frameR Z (NeZero.pos Z) (v+1) f 1 n.natAbs) := by
    apply hRow
    intro p hp
    simpa only [Int.natAbs_natCast] using lt_of_lt_of_le (pow_pos (by norm_num : (0:ℕ)<2) j)
      (Finset.mem_Ico.mp hp).1
  have hN : nRow (fun n => printedCoeff Z v true f n.natAbs) =
      (scale v : ℂ) * nRow (fun n => frameR Z (NeZero.pos Z) (v+1) f cuspOneMatrix n.natAbs) :=
    hRow v true _ _ _ (fun n hn => traceIndex_natAbs_pos D k negativeM Z hn ha) f
  have hsq : ((scale v : ℝ) : ℂ)^2 =
      (4*(Real.pi : ℂ))*(Real.Gamma (2*((v+1:ℕ):ℝ)) : ℂ) := by
    have h : (scale v)^2 = 4*Real.pi*Real.Gamma (2*((v+1:ℕ):ℝ)) := by
      simpa only [Nat.cast_add,Nat.cast_one,mul_add,mul_one] using scale_sq v
    exact_mod_cast h
  have pull (s a b : ℂ) : (s*a)*(s*b)=s^2*(a*b) := by ring
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold markedCoordinate hProduct
  change _ = _ * ((star (mRow (fun n => printedCoeff Z v false f n.natAbs)) *
    nRow (fun n => printedCoeff Z v true f n.natAbs))/(2*(Real.pi : ℂ)))
  rw [hM,hN,star_mul',show star ((scale v:ℝ):ℂ) = (scale v:ℂ) from Complex.conj_ofReal _,
    pull,hsq]
  dsimp only [f]
  field_simp [hπ] <;> ring

/-- Spectral rows evaluated on the prescribed test and original composite
marks. The source sign determines the J/Petersson or K branch. -/
def printedRow (N : ℝ) : ℂ :=
  let Y := chartY0 D k upper j N
  let Φ := spectralTest ell Y
  let E := eProduct D r k z upper negativeM J j ell
  let M₁ := mProduct D r k z upper negativeM J j ell
  if traceNegative D k negativeM then
    (∑' i, (8*kTransform (basisOrder Z (NeZero.pos Z) i) Φ)*(M₁ i/4))+
      ∫ t : ℝ, (oppositeWeight Φ t/4)*E t
  else
    (∑' v : ℕ, ∑ i, (holWeight v Φ/2)*hProduct D r k z upper negativeM J j ell v i)+
      ((∑' i, nativeWeight Z Φ i*(M₁ i/4))+
        ∫ t : ℝ, (positiveWeight Φ t/4)*E t)

private theorem pos_eq (ha : D.block.atom.residue ≠ 0) (hs : traceNegative D k negativeM=false)
    (N : ℝ) : positiveRow D r k z upper negativeM J j ell N =
      printedRow D r k z upper negativeM J j ell N := by
  simp only [printedRow, hs, Bool.false_eq_true, if_false, positiveRow, scalar, total, markedWeight,
    pos_line D r k z upper negativeM J j ell ha, mProduct_native D r k z upper negativeM J j ell ha,
    hProduct_native D r k z upper negativeM J j ell ha]

private theorem neg_eq (ha : D.block.atom.residue ≠ 0) (hs : traceNegative D k negativeM=true)
    (N : ℝ) : rowSpectrum D r k z upper negativeM J j ell N =
      printedRow D r k z upper negativeM J j ell N := by
  simp only [printedRow,hs,if_true,rowSpectrum,
    neg_line D r k z upper negativeM J j ell ha]
  have hd := mProduct_native D r k z upper negativeM J j ell ha
  simp only [dMark] at hd
  simp_rw [hd]

/-- The unmodified arithmetic whole-modulus level has exactly these three
normalized coefficient products, on an actual occupied level of either sign. -/
theorem original_printed_geometric_at_level (ha : D.block.atom.residue ≠ 0)
    (M : ℝ) {N : ℝ} (hN : 0<N) (hz : Z ∈ chartLevels D k upper) :
    (∑ n ∈ nCarrier D k Z, ∑ p ∈ commonMBlock J j,
      fullModulusRow D r k upper J j negativeM M N ell Z n p) =
      (((M*Real.sqrt (fixedZ D upper):ℝ):ℂ)*printedRow D r k z upper negativeM J j ell N) := by
  cases h : traceNegative D k negativeM with
  | false => rw [full_level_positive D r k z ha upper negativeM h J j ell M hN hz,
      pos_eq D r k z upper negativeM J j ell ha h]
  | true => rw [full_level_row D r k z ha upper negativeM h J j ell M hN hz,
      neg_eq D r k z upper negativeM J j ell ha h]
end Row

def printedChart (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (upper negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  (((M * Real.sqrt (fixedZ D upper) : ℝ) : ℂ) *
    ∑ z ∈ (chartLevels D k upper).attach,
      printedRow D r k ⟨z.val,chartLevels_subset D k upper z.property⟩ upper negativeM J j ell N)

def printedBlock (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (J j : ℕ) (negativeM : Bool) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  actualCoeff ((2^j : ℕ)*M/N) (if negativeM then -1 else 1) ell *
    (printedChart D r k false negativeM J j M N ell + printedChart D r k true negativeM J j M N ell)

def printedPiece (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  ∑ k ∈ originalKeys D, ∑ j ∈ blockIndices J,
    (printedBlock D r k J j (positiveLane D k) M N ell +
      printedBlock D r k J j (!(positiveLane D k)) M N ell)

private theorem both_eq (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (ha : D.block.atom.residue ≠ 0) (J : ℕ) (M N : ℝ) (ell : D4 → ℤ) :
    bothPiece D r J M N ell = printedPiece D r J M N ell := by
  unfold bothPiece printedPiece
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  have h := opposite_lanes D k
  have hp (z : Row D k) (u : Bool) := pos_eq D r k z u (positiveLane D k) J j ell ha h.1 N
  have hn (z : Row D k) (u : Bool) := neg_eq D r k z u (!(positiveLane D k)) J j ell ha h.2 N
  simp only [positiveBlock, oppositeBlockSpectrum, printedBlock, positiveChart, chartSpectrum,
    printedChart, hp, hn]

def printedSix (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J : ℕ) (ell : D4 → ℤ) : ℂ :=
  printedPiece D r J D.bScale D.cScale ell +
  printedPiece D r J D.bScale (2*D.cScale) ell +
  printedPiece D r J D.bScale (4*D.cScale) ell +
  printedPiece D r J (2*D.bScale) D.cScale ell +
  printedPiece D r J (2*D.bScale) (2*D.cScale) ell +
  printedPiece D r J (2*D.bScale) (4*D.cScale) ell

/-- Both physical sign lanes, six actual scales, the original outer Fourier
sum and its exact remainder. Absolute summability remains outside each
completed spectral evaluation. -/
theorem original_printed_six_spectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (x ε : ℝ) (L : ℕ) (ha : D.block.atom.residue ≠ 0) :
    let J := globalCutoff D x ε
    (smoothSix D r : ℂ) = sixRemainder D r J + (∑' ell, printedSix D r J ell) ∧
      Summable (fun ell : D4 → ℤ => ‖printedSix D r J ell‖) := by
  let J := globalCutoff D x ε
  have he : bothSix D r J = printedSix D r J := by
    funext ell
    simp only [bothSix, printedSix, both_eq D r ha]
  refine ⟨?_,?_⟩
  · simpa only [J] using (original_six_spectrum D r x ε L ha).trans
      (congrArg (fun f : (D4 → ℤ) → ℂ => sixRemainder D r J + ∑' ell, f ell) he)
  · simpa only [← he] using (both_six_summable D r J L ha)

end ImbalancedChen.Part3.OriginalPrintedPrescribedRows20261123
end
