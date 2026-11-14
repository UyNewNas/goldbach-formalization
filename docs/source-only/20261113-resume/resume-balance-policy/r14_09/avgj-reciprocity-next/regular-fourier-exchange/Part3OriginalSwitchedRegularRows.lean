import ImbalancedChen.Part3OriginalSwitchedRegularMarkExchange
import ImbalancedChen.Part3OriginalSwitchedNativeBilinearTrace

/-! The two independently shifted linear forms inside the full
discrete and continuous Fourier-mode exchanges. -/
namespace ImbalancedChen.Part3.OriginalSwitchedRegularRows20261113
noncomputable section
open Finset Complex MeasureTheory
open scoped BigOperators Classical MatrixGroups
open OriginalSwitchedRegularMarkExchange20261113
open OriginalSwitchedRegularFourierBudget20261113 (scaled term)
open OriginalSwitchedSeparatedTransforms20261113 (factor)
open OriginalSwitchedSeparatedBlocks20261113 (multiplier block rowSum)
open private rephase from ImbalancedChen.Part3OriginalSwitchedSeparatedBlocks
open private mark from ImbalancedChen.Part3OriginalSwitchedNativeBilinearTrace
open OriginalSwitchedSeparatedNativeSlots20261113 (legs)
open OriginalSwitchedFourCoordinateRows20261113 (ratio)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open ActualCuspBasisWhittakerCoefficients20261102 (basisR)
open ActualContinuousClassFourier20261110 (nativeR)
open OriginalContinuousCuspGram20261110 (nativeProduct)
open ActualCuspDenominatorClasses20261110 (Parameters)
open OriginalSameInfinityTensorSpectrum20261113 (disc cont)
open OriginalSwitchedCutoffModes20261113 (mode)
open ActualUnitBandSpectralMass20261112 (exceptional height)
open ActualFullCuspEigenbasis20261026b
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def amplitude (u : ℕ→ℂ) (ω : ℝ) (m n : ℕ) := star (phaseAt ω m*u m)*(phaseAt ω n*u n)

private theorem joined (j : ℕ) (ω Y Q : ℝ) (d : ℕ+) (k : D4→ℤ) (u R : ℕ→ℂ) (c : ℂ) :
    (∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),
      amplitude u ω m.val n.val*((factor j Y Q d k m.val n.val*c)*(star (R m.val)*R n.val)))=
      multiplier k (ratio (j:=j) Y Q d)*c*legs j ω k (fun m => u m*R m) := by
  rw [show multiplier k (ratio (j:=j) Y Q d)*c*legs j ω k (fun m => u m*R m)=
      block j ω (fun m => u m*R m) (fun m => u m*R m) (fun m n => factor j Y Q d k m n*c) by
    rw [rephase]
    dsimp only [legs];ring]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  simp only [amplitude,star_mul']
  ring

def D (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ)
    (k : D4→ℤ) (i : actualCuspBasisIndex d.val (NeZero.pos d.val)) :=
  if exceptional d.val i then 0 else
    multiplier k (ratio (j:=j) Y Q d)*scaled (spectralTest (mode (k 0)) Y⁻¹) (height d.val i)*
      legs j ω k (fun m => u m*basisR d.val (NeZero.pos d.val) i 1 (m:ℤ))

def E (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) (k : D4→ℤ) (t : ℝ) :=
  ∑ a : Parameters d.val,multiplier k (ratio (j:=j) Y Q d)*scaled (spectralTest (mode (k 0)) Y⁻¹) t*
    legs j ω k (fun m => u m*nativeR a false (m:ℤ) t)/(4*(Real.pi:ℂ))

theorem discrete_rows (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) (k : D4→ℤ)
    (i : actualCuspBasisIndex d.val (NeZero.pos d.val)) :
    (∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),amplitude u ω m.val n.val*
      discreteMode d (mark m) (mark n) j Y Q k i)=D d j Y Q ω u k i := by
  by_cases hi : exceptional d.val i
  · simp [discreteMode,D,hi]
  · simpa only [discreteMode,D,if_neg hi,term,disc,mark] using
      joined j ω Y Q d k u (fun m => basisR d.val (NeZero.pos d.val) i 1 (m:ℤ))
        (scaled (spectralTest (mode (k 0)) Y⁻¹) (height d.val i))

theorem incoming_rows (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) (k : D4→ℤ) (t : ℝ) :
    (∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),amplitude u ω m.val n.val*
      incomingMode d (mark m) (mark n) j Y Q k t)=E d j Y Q ω u k t := by
  let I := ↥(dyadicWindow j)
  let P := Parameters d.val
  let c := scaled (spectralTest (mode (k 0)) Y⁻¹) t
  let δ : ℂ := 4*(Real.pi:ℂ)
  let A := fun (m n : I) => amplitude u ω m.val n.val
  let R := fun (a : P) (m : ℕ) => nativeR a false (m:ℤ) t
  let V := fun (m n : I) => factor j Y Q d k m.val n.val*c
  let Z := fun (m n : I) (a : P) => A m n*(V m n*(star (R a m.val)*R a n.val))
  calc
    _ = ∑ m : I,∑ n : I,∑ a : P,Z m n a/δ := by
      simp only [incomingMode,term,cont,nativeProduct,Finset.mul_sum,mark]
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro a _
      dsimp only [Z,A,V,R,δ,c];ring
    _ = ∑ a : P,(∑ m : I,∑ n : I,Z m n a)/δ := by
      simp only [Finset.sum_div]
      rw [sum_comm (s:=(univ:Finset P)) (t:=(univ:Finset I))]
      apply sum_congr rfl
      intro m _
      rw [sum_comm (s:=(univ:Finset P)) (t:=(univ:Finset I))]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      exact congrArg (fun s : ℂ => s/δ) (joined j ω Y Q d k u (R a) c)

end
end ImbalancedChen.Part3.OriginalSwitchedRegularRows20261113
