import ImbalancedChen.Part3OriginalSwitchedSeparatedBlocks
import ImbalancedChen.Part3OriginalSwitchedNativeBilinearTrace

/-! Instantiate both linear factors on the actual identity-frame
principal, incoming-cusp and positive-weight Fourier coefficients. -/
namespace ImbalancedChen.Part3.OriginalSwitchedSeparatedNativeSlots20261113
noncomputable section
open Complex
open scoped BigOperators MatrixGroups
open OriginalSwitchedSeparatedBlocks20261113
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalSwitchedCutoffModes20261113 (mode)
open OriginalSwitchedFourCoordinateRows20261113 (ratio)
open ActualPositiveNativeDiagonal20261112 (nativeWeight)
open ActualUnitBandSpectralMass20261112 (height exceptional)
open ActualFullCuspEigenbasis20261026b ActualCuspBasisIndexCounting20261026b
open ActualCuspBasisWhittakerCoefficients20261102 (basisR)
open ActualContinuousClassFourier20261110 (nativeR)
open ActualCuspDenominatorClasses20261110 (Parameters)
open ActualPrescribedPositiveJ20261112 (positiveWeight)
open ActualPositiveHolomorphicWeights20261112 (holWeight)
open OriginalHolomorphicCuspFrames20261110 (frameR)
open OriginalHolomorphicPeterssonSpace20261112 (BasisIndex formsBasis)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)

local instance (d : ℕ+) : NeZero d.val := ⟨d.property.ne'⟩

def legs (j : ℕ) (ω : ℝ) (k : D4→ℤ) (R : ℕ→ℂ) :=
  star (rowSum j (ω-(k 1:ℝ)/(64*classicalMScale j)) R)*
    rowSum j (ω+(k 2:ℝ)/(64*classicalMScale j)) R

private theorem regular_scaled (j : ℕ) (ω : ℝ) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q)
    (d : ℕ+) (t : ℝ) (R : ℕ→ℂ) (c : ℂ) :
    HasSum (fun k : D4→ℤ => multiplier k (ratio (j:=j) Y Q d)*
      (positiveWeight (spectralTest (mode (k 0)) Y⁻¹) t/c)*legs j ω k R)
        (block j ω R R (fun m n => positiveWeight (switchedTest Y ((d.val:ℝ)*Q) m n) t)/c) := by
  exact ((principal_block j ω yp qp d t R R).div_const c).congr_fun
    (fun k => by dsimp only [legs];ring)

theorem discrete_slot (j : ℕ) (ω : ℝ) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q)
    (d : ℕ+) (i : actualCuspBasisIndex d.val (NeZero.pos d.val)) (reg : ¬exceptional d.val i) :
    let R := fun m : ℕ => basisR d.val (NeZero.pos d.val) i 1 (m:ℤ)
    HasSum (fun k : D4→ℤ => multiplier k (ratio (j:=j) Y Q d)*
      nativeWeight d.val (spectralTest (mode (k 0)) Y⁻¹) i*legs j ω k R)
      (block j ω R R (fun m n => nativeWeight d.val (switchedTest Y ((d.val:ℝ)*Q) m n) i)) := by
  dsimp only
  let R := fun m : ℕ => basisR d.val (NeZero.pos d.val) i 1 (m:ℤ)
  have H := regular_scaled j ω yp qp d (height d.val i) R (Real.cosh (Real.pi*height d.val i):ℂ)
  simpa only [nativeWeight,if_neg reg,block,Finset.sum_div,mul_div_assoc,R] using H

theorem incoming_slot (j : ℕ) (ω : ℝ) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q)
    (d : ℕ+) (a : Parameters d.val) (t : ℝ) :
    let R := fun m : ℕ => nativeR a false (m:ℤ) t
    let c := (4*(Real.pi:ℂ))*(Real.cosh (Real.pi*t):ℂ)
    HasSum (fun k : D4→ℤ => multiplier k (ratio (j:=j) Y Q d)*
      (positiveWeight (spectralTest (mode (k 0)) Y⁻¹) t/c)*legs j ω k R)
      (block j ω R R (fun m n => positiveWeight (switchedTest Y ((d.val:ℝ)*Q) m n) t)/c) :=
  regular_scaled j ω yp qp d t _ _

theorem positive_weight_slot (j : ℕ) (ω : ℝ) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q)
    (d : ℕ+) (h : ℕ) (i : BasisIndex d.val (h+1)) :
    let R := fun m : ℕ => frameR d.val (NeZero.pos d.val) (h+1) (formsBasis d.val (h+1) i) 1 m
    let G := (Real.Gamma (2*((h+1:ℕ):ℝ)):ℂ)
    HasSum (fun k : D4→ℤ => multiplier k (ratio (j:=j) Y Q d)*
      (G*holWeight h (spectralTest (mode (k 0)) Y⁻¹))*legs j ω k R)
      (G*block j ω R R (fun m n => holWeight h (switchedTest Y ((d.val:ℝ)*Q) m n))) := by
  dsimp only
  exact ((holomorphic_block j ω yp qp d h _ _).mul_left _).congr_fun
    (fun k => by dsimp only [legs];ring)

end
end ImbalancedChen.Part3.OriginalSwitchedSeparatedNativeSlots20261113
