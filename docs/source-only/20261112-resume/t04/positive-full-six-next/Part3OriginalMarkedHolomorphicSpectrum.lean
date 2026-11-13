import ImbalancedChen.Part3OriginalPrescribedPositiveTrace
import ImbalancedChen.Part3OriginalHolomorphicWeightSum
import Batteries.Tactic.OpenPrivate

/-! Regroup the original two finite marks inside every actual even-weight
Petersson basis. Both m and source functionals are the manuscript ones. -/
namespace ImbalancedChen.Part3.OriginalMarkedHolomorphicSpectrum20261112
noncomputable section
open Complex
open scoped Classical BigOperators MatrixGroups ComplexConjugate
open OriginalHolomorphicPeterssonSpace20261112 (formsBasis BasisIndex)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicCuspFrames20261110 (frameR)
open Gamma0ActualCuspsSourceOnly (cuspOneMatrix)
open ActualPositiveHolomorphicWeights20261112 (holWeight)
open OriginalHolomorphicWeightSum20261112 (holSpectrum basisTerm weighted_petersson original_holomorphic_projection)
open OriginalPrescribedPositiveTrace20261112 (holomorphic)
open OriginalPositiveCompactPretrace20261112 (marking)
open OriginalPositiveScalarGeometry20261112 (positive_row_index)
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalSignedTraceInput20261102 OriginalTwoZFourierAssembly20261102
open OriginalContinuousClassRemoval20261110 (markedRow M source)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4→ℤ)
local instance nzLevel : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩

def markedCoordinate (Y : ℝ) (v : ℕ) (i : BasisIndex z.val (v+1)) : ℂ :=
  (Real.Gamma (2*((v+1:ℕ):ℝ)):ℂ)*holWeight v (spectralTest ell Y)*
    (star (M J j ell (fun h => frameR z.val (NeZero.pos z.val) (v+1) (formsBasis z.val (v+1) i) 1 h.natAbs))*
      source D r k z upper negativeM ell (fun h =>
        frameR z.val (NeZero.pos z.val) (v+1) (formsBasis z.val (v+1) i) cuspOneMatrix h.natAbs))

def markedWeight (Y : ℝ) (v : ℕ) := ∑ i,markedCoordinate D r k z upper negativeM J j ell Y v i

private theorem coordinate_eq (Y : ℝ) (v : ℕ) (i : BasisIndex z.val (v+1)) :
    markedCoordinate D r k z upper negativeM J j ell Y v i =
      marking D r k z upper negativeM J j ell (fun p b => basisTerm z.val p b.natAbs (spectralTest ell Y) v i) := by
  let A := fun p : ℕ => frameR z.val (NeZero.pos z.val) (v+1) (formsBasis z.val (v+1) i) 1 p
  let B := fun n : ℕ => frameR z.val (NeZero.pos z.val) (v+1) (formsBasis z.val (v+1) i) cuspOneMatrix
    (traceIndex D k negativeM z.val n).natAbs
  let T := (Real.Gamma (2*((v+1:ℕ):ℝ)):ℂ)*holWeight v (spectralTest ell Y)
  let w := (commonPoissonCompleted J j (ell 1)).weight
  let β := traceBeta D r k upper negativeM ell z.val
  have m : star (M J j ell (fun h => A h.natAbs))=∑ p∈commonMBlock J j,w p*star (A p) := by
    simp only [M,markedRow,star_sum,star_mul',star_star,Int.natAbs_natCast,w]
  change T*(star (M J j ell (fun h => A h.natAbs))*(∑ n∈nCarrier D k z.val,β n*B n))=_
  rw [m,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  rw [Finset.sum_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _
  dsimp only [basisTerm,T,w,β,A,B,Complex.star_def]; ring

private theorem fixed_weight (Y : ℝ) (v : ℕ) :
    markedWeight D r k z upper negativeM J j ell Y v =
      marking D r k z upper negativeM J j ell (fun p b => ∑ i,basisTerm z.val p b.natAbs (spectralTest ell Y) v i) := by
  simp only [markedWeight,coordinate_eq,marking,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro n _; rw [Finset.sum_comm]

/-- Absolute convergence on the dependent set of all weights and all vectors
within each weight, after inserting both original finite functionals. -/
theorem marked_absolute (ha : D.block.atom.residue≠0) (hs : traceNegative D k negativeM=false)
    {Y : ℝ} (hY : 0<Y) :
    Summable (fun a : Σ v : ℕ,BasisIndex z.val (v+1) => ‖markedCoordinate D r k z upper negativeM J j ell Y a.1 a.2‖) := by
  let W := (commonPoissonCompleted J j (ell 1)).weight
  let β := traceBeta D r k upper negativeM ell z.val
  have P (n : ℕ) (hn : n∈nCarrier D k z.val) (p : ℕ) (hp : p∈commonMBlock J j) :=
    (original_holomorphic_projection D k negativeM ha hs z.val J j hp hn ell hY).2.1.of_norm.mul_left (W p*β n)
  have S := summable_sum (s:=nCarrier D k z.val) fun n hn => summable_sum (s:=commonMBlock J j) fun p hp => P n hn p hp
  exact S.norm.congr (fun a => (congrArg norm (coordinate_eq D r k z upper negativeM J j ell Y a.1 a.2)).symm)

theorem marked_holomorphic (ha : D.block.atom.residue≠0) (hs : traceNegative D k negativeM=false)
    {Y : ℝ} (hY : 0<Y) :
    Summable (fun v : ℕ => ‖markedWeight D r k z upper negativeM J j ell Y v‖) ∧
      HasSum (markedWeight D r k z upper negativeM J j ell Y)
        (holomorphic D r k z upper negativeM J j ell Y) := by
  let Φ := spectralTest ell Y
  let h := traceIndex D k negativeM z.val
  have e (n : ℕ) (hn : n∈nCarrier D k z.val) (p : ℕ) (hp : p∈commonMBlock J j) :
      HasSum (fun v : ℕ => ∑ i,basisTerm z.val p (h n).natAbs Φ v i) (holSpectrum z.val p (h n).natAbs Φ) := by
    have pp := lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) (Finset.mem_Ico.mp hp).1
    have hb := positive_row_index D k negativeM hn ha hs
    exact (weighted_petersson z.val p (h n).natAbs pp (Int.natAbs_pos.mpr hb.ne') ell hY).2.2.1.of_norm.hasSum
  have S := hasSum_sum (fun n (hn : n∈nCarrier D k z.val) => hasSum_sum (fun p (hp : p∈commonMBlock J j) =>
    (e n hn p hp).mul_left ((commonPoissonCompleted J j (ell 1)).weight p*traceBeta D r k upper negativeM ell z.val n)))
  have R : HasSum (markedWeight D r k z upper negativeM J j ell Y) (holomorphic D r k z upper negativeM J j ell Y) :=
    S.congr_fun (fixed_weight D r k z upper negativeM J j ell Y)
  exact ⟨R.summable.norm,R⟩

end
end ImbalancedChen.Part3.OriginalMarkedHolomorphicSpectrum20261112
