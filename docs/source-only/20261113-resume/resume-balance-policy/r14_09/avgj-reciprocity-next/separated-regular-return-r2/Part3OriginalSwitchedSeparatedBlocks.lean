import ImbalancedChen.Part3OriginalSwitchedSeparatedTransforms

/-! Contract the separated frequency modes against both actual marks.
The level phase, window and radial transform are outside both sums. -/
namespace ImbalancedChen.Part3.OriginalSwitchedSeparatedBlocks20261113
noncomputable section
open Finset Complex
open scoped BigOperators
open OriginalSwitchedFourCoordinateSymbol20261113 (coefficient)
open OriginalSwitchedFourCoordinateRows20261113 (phase ratio)
open OriginalSwitchedSeparatedTransforms20261113 (factor principal holomorphic)
open OriginalSwitchedCutoffModes20261113 (mode)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e spectralTest)
open ActualPrescribedPositiveJ20261112 (positiveWeight)
open ActualPositiveHolomorphicWeights20261112 (holWeight)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)

def multiplier (k : D4→ℤ) (ζ : ℝ) := if ζ∈Set.Icc (1/8:ℝ) 8 then coefficient k*e ((k 3:ℝ)/64*ζ) else 0

def rowSum (j : ℕ) (ω : ℝ) (A : ℕ→ℂ) := ∑ m : ↥(dyadicWindow j),phaseAt ω m.val*A m.val

def block (j : ℕ) (ω : ℝ) (A B : ℕ→ℂ) (W : ℕ→ℕ→ℂ) :=
  ∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),
    star (phaseAt ω m.val*A m.val)*(phaseAt ω n.val*B n.val)*W m.val n.val

private theorem add_shift (ω a : ℝ) (m : ℕ) :
    phaseAt (ω+a) m=phaseAt ω m*e (a*(m:ℝ)) := by
  unfold phaseAt e
  rw [←Complex.exp_add]
  congr 1
  push_cast;ring

private theorem minus_shift (ω a : ℝ) (m : ℕ) :
    star (phaseAt (ω-a) m)=star (phaseAt ω m)*e (a*(m:ℝ)) := by
  rw [sub_eq_add_neg,add_shift,star_mul']
  have h : star (e ((-a)*(m:ℝ)))=e (a*(m:ℝ)) := by
    unfold e
    rw [Complex.star_def,←Complex.exp_conj]
    congr 1
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,map_ofNat]
    push_cast;ring
  rw [h]

private theorem rephase (j : ℕ) (ω Y Q : ℝ) (d : ℕ+) (k : D4→ℤ) (A B : ℕ→ℂ) (T : ℂ) :
    block j ω A B (fun m n => factor j Y Q d k m n*T)=
      multiplier k (ratio (j:=j) Y Q d)*T*
        star (rowSum j (ω-(k 1:ℝ)/(64*classicalMScale j)) A)*
        rowSum j (ω+(k 2:ℝ)/(64*classicalMScale j)) B := by
  classical
  let M := classicalMScale j
  let ζ := ratio (j:=j) Y Q d
  have p (m n : ℕ) :
      star (phaseAt ω m*A m)*(phaseAt ω n*B n)*(factor j Y Q d k m n*T)=
      multiplier k ζ*T*(star (phaseAt (ω-(k 1:ℝ)/(64*M)) m*A m)*
        (phaseAt (ω+(k 2:ℝ)/(64*M)) n*B n)) := by
    simp only [star_mul',minus_shift,add_shift]
    have e1 : (k 1:ℝ)/(64*M)*(m:ℝ)=(k 1:ℝ)/64*((m:ℝ)/M) := by
      simp only [div_eq_mul_inv,mul_inv_rev];ring
    have e2 : (k 2:ℝ)/(64*M)*(n:ℝ)=(k 2:ℝ)/64*((n:ℝ)/M) := by
      simp only [div_eq_mul_inv,mul_inv_rev];ring
    rw [e1,e2]
    unfold factor multiplier phase
    by_cases h : ζ∈Set.Icc (1/8:ℝ) 8
    · simp only [if_pos h];ring
    · simp only [if_neg h,zero_mul,mul_zero]
  unfold block
  simp_rw [p]
  unfold rowSum
  rw [star_sum]
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul]
  ring

private theorem contracted (j : ℕ) (ω Y Q : ℝ) (d : ℕ+) (A B : ℕ→ℂ)
    (T : (D4→ℤ)→ℂ) (W : ℕ→ℕ→ℂ)
    (h : ∀ m∈dyadicWindow j,∀ n∈dyadicWindow j,HasSum (fun k => factor j Y Q d k m n*T k) (W m n)) :
    HasSum (fun k => multiplier k (ratio (j:=j) Y Q d)*T k*
      star (rowSum j (ω-(k 1:ℝ)/(64*classicalMScale j)) A)*
      rowSum j (ω+(k 2:ℝ)/(64*classicalMScale j)) B) (block j ω A B W) := by
  let U := ↥(dyadicWindow j)
  have H := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset U)) =>
    hasSum_sum (s:=univ) (fun n (_ : n∈(univ:Finset U)) =>
      (h m.val m.property n.val n.property).mul_left
        (star (phaseAt ω m.val*A m.val)*(phaseAt ω n.val*B n.val))))
  exact H.congr_fun (fun k => (rephase j ω Y Q d k A B (T k)).symm)

/-- The functions A and B are the two genuine coefficient rows of any
given basis vector or continuous channel. This equality is uniform in them. -/
theorem principal_block (j : ℕ) (ω : ℝ) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+)
    (t : ℝ) (A B : ℕ→ℂ) :
    HasSum (fun k : D4→ℤ => multiplier k (ratio (j:=j) Y Q d)*
      positiveWeight (spectralTest (mode (k 0)) Y⁻¹) t*
      star (rowSum j (ω-(k 1:ℝ)/(64*classicalMScale j)) A)*
      rowSum j (ω+(k 2:ℝ)/(64*classicalMScale j)) B)
      (block j ω A B (fun m n => positiveWeight (switchedTest Y ((d.val:ℝ)*Q) m n) t)) :=
  contracted j ω Y Q d A B _ _ (fun _ hm _ hn => principal hm hn yp qp d t)

theorem holomorphic_block (j : ℕ) (ω : ℝ) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+)
    (h : ℕ) (A B : ℕ→ℂ) :
    HasSum (fun k : D4→ℤ => multiplier k (ratio (j:=j) Y Q d)*
      holWeight h (spectralTest (mode (k 0)) Y⁻¹)*
      star (rowSum j (ω-(k 1:ℝ)/(64*classicalMScale j)) A)*
      rowSum j (ω+(k 2:ℝ)/(64*classicalMScale j)) B)
      (block j ω A B (fun m n => holWeight h (switchedTest Y ((d.val:ℝ)*Q) m n))) :=
  contracted j ω Y Q d A B _ _ (fun _ hm _ hn => holomorphic hm hn yp qp d h)

end
end ImbalancedChen.Part3.OriginalSwitchedSeparatedBlocks20261113
